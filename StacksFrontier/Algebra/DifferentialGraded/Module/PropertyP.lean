module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Isomorphisms
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.AdmissibleCriterion
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover
public import StacksFrontier.Algebra.DifferentialGraded.PropertyPResolution
public import StacksCore.Tactic.StacksAttribute
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Property-(P) resolutions of bundled differential graded modules

Let `R` be a commutative ring and `(A, d)` a differential graded `R`-algebra. A right
differential graded `A`-module `P` has *property (P)* when it carries an exhaustive increasing
filtration `0 = F_{-1} P ⊆ F_0 P ⊆ F_1 P ⊆ ⋯` by differential graded submodules whose inclusions
are admissible monomorphisms and whose successive quotients are direct sums of shifts `A[k]` of
the algebra. This file proves that every differential graded module receives a quasi-isomorphism
from a module with property (P), in the bundled `DifferentialGradedAlgebra` /
`DifferentialGradedModule` interface used throughout the chapter, and with the conclusion
expressed by Mathlib's `QuasiIso` applied to the underlying cochain map.

## Main definitions

* `DifferentialGradedModule.directSumShifts`: the direct sum of shifts `⨁ i, A[k i]`, as a
  bundled differential graded `A`-module.
* `DifferentialGradedModule.PropertyPFiltration`: the data of a filtration exhibiting
  property (P).
* `DifferentialGradedModule.IsQuasiIsomorphism`: the cycle-and-boundary criterion for being a
  quasi-isomorphism.

## Main results

* `DifferentialGradedModule.quasiIso_of_isQuasiIsomorphism`: the cycle-and-boundary criterion
  implies that the underlying cochain map is a quasi-isomorphism in Mathlib's sense.
* `DifferentialGradedModule.exists_propertyP_resolution`: every differential graded module `M`
  receives a quasi-isomorphism from a differential graded module `P` carrying a property-(P)
  filtration.

## Implementation notes

The mathematical content is `Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution`,
proved for the *unbundled* encoding `Stacks.DifferentialGraded.DGAlgebra` /
`Stacks.DifferentialGraded.DGModule`, in which the data of a differential graded module and its
laws are recorded separately. This file transports that theorem to the bundled encoding of
Stacks Tag 09JJ, which is what the rest of the chapter consumes. The transport is by the
conversions of the namespace `DifferentialGradedModule.Unbundled`:
`DifferentialGraded.NativeCover.Native.grading` promotes the additive grading of the unbundled
encoding to the `R`-submodule grading the bundled one asks for, and the laws of an unbundled
module supply the proof-carrying fields of a bundled one.

The bundled encoding of Tag 09JJ is *single-universe*: the base ring, the algebra and every
module live in one universe `u`. The Stacks source is universe-polymorphic, and so is the
unbundled development (the resolution of a module in universe `w` over an algebra in universe `v`
has carrier in `max v w`); the statements here are the single-universe case. In particular the
cell index types of a `PropertyPFiltration` are in `Type u`.

Being a quasi-isomorphism is first obtained in the cycle-and-boundary form `IsQuasiIsomorphism`,
which is what the unbundled development produces, and then converted to
`QuasiIso ((forgetToCochainComplex A).map f)` through the explicit left homology data of a short
complex of modules, for which the homology object is literally `ker g / range f`.

## References

* [Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum

namespace DifferentialGradedModule

universe u

/-! ### Transport between the unbundled and the bundled encoding

The declarations of this namespace are plumbing: they translate between the unbundled encoding
`Stacks.DifferentialGraded.DGModule`, in which the laws of a differential graded module are a
separate predicate, and the bundled encoding of Stacks Tag 09JJ, in which they are fields.
They are public only because `directSumShifts` is defined by them. -/

namespace Unbundled

variable {R : Type u} [CommRing R]

/-- The two encodings of the sign `(-1)^n` agree: `Int.negOnePow`, cast to `ℤ`, is the integer
power `(-1)^|n|`. -/
theorem negOnePow_cast (n : ℤ) : (n.negOnePow : ℤ) = (-1 : ℤ) ^ n.natAbs := by
  simpa only [Int.cast_id] using Int.coe_negOnePow ℤ n

/-- The unbundled differential graded algebra underlying a bundled one: the same carrier,
grading and differential, with the laws recorded separately. -/
abbrev algebra (A : DifferentialGradedAlgebra.{u, u} R) : Stacks.DifferentialGraded.DGAlgebra R
  where
  carrier := A.A
  grading := A.grading
  d := A.d

/-- The laws of a bundled differential graded algebra, in unbundled form. -/
theorem algebra_isLawful (A : DifferentialGradedAlgebra.{u, u} R) : (algebra A).IsLawful where
  d_mem := A.d_mem
  d_comp_d x := LinearMap.congr_fun A.d_comp_d x
  leibniz n m a b ha hb := by
    simpa only [negOnePow_cast] using A.leibniz n m a b ha hb

variable {A : DifferentialGradedAlgebra.{u, u} R}

/-- The right `A`-action on an unbundled differential graded module, in the spelling `A.Aᵐᵒᵖ`
used by the bundled encoding rather than `(algebra A).carrierᵐᵒᵖ`.

The two spellings are equal by definition, but instance search unfolds `algebra` and then
cannot match the resulting `A.Aᵐᵒᵖ` against the pattern `?B.carrierᵐᵒᵖ` of
`Stacks.DifferentialGraded.DGModule.moduleA`, so neither spelling is found by synthesis. Stating
the action once at the bundled spelling repairs both. -/
instance moduleOp (M : Stacks.DifferentialGraded.DGModule (algebra A)) : Module A.Aᵐᵒᵖ M.carrier :=
  M.moduleA

/-- The unbundled differential graded module underlying a bundled one. -/
abbrev module (M : DifferentialGradedModule.{u, u, u} A) : Stacks.DifferentialGraded.DGModule
  (algebra A) where
  carrier := M.M
  smul_def r x := (IsScalarTower.algebraMap_smul A.Aᵐᵒᵖ r x).symm
  grading n := (M.grading n).toAddSubgroup
  d := M.d

/-- The laws of a bundled differential graded module, in unbundled form. -/
theorem module_isLawful (M : DifferentialGradedModule.{u, u, u} A) : (module M).IsLawful where
  isInternal := DirectSum.Decomposition.isInternal M.grading
  grading_smul := M.smul_mem
  d_mem := M.d_mem
  d_comp_d x := LinearMap.congr_fun M.d_comp_d x
  leibniz n m x a hx ha := by
    simpa only [negOnePow_cast] using M.leibniz n m x a hx ha

/-- A lawful unbundled differential graded module, as a bundled one. The grading is promoted
from additive subgroups to `R`-submodules by `DifferentialGraded.NativeCover.Native.grading`, and
the internality of that grading provides the direct-sum decomposition the bundled encoding asks
for. -/
abbrev bundle {M : Stacks.DifferentialGraded.DGModule (algebra A)} (hM : M.IsLawful) :
    DifferentialGradedModule.{u, u, u} A where
  M := M.carrier
  addCommGroup := M.addCommGroup
  module := M.moduleR
  rmodule := M.moduleA
  isScalarTower := IsScalarTower.of_algebraMap_smul (fun r x => (M.smul_def r x).symm)
  grading := DifferentialGraded.NativeCover.Native.grading M hM
  decomposition := (show DirectSum.IsInternal (DifferentialGraded.NativeCover.Native.grading M hM)
    from hM.isInternal).chooseDecomposition
  smul_mem := hM.grading_smul
  d := M.d
  d_comp_d := LinearMap.ext hM.d_comp_d
  d_mem := hM.d_mem
  leibniz n m x a hx ha := by
    simpa only [negOnePow_cast] using hM.leibniz n m x a hx ha

/-- An `Aᵐᵒᵖ`-linear map between unbundled differential graded modules, viewed as the
`R`-linear map the bundled encoding asks for. -/
def restrictR {M N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (f : M.carrier →ₗ[(algebra A).carrierᵐᵒᵖ] N.carrier) : M.carrier →ₗ[R] N.carrier where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    rw [M.smul_def, N.smul_def, map_smul]
    rfl

/-- `restrictR f` acts as `f`. -/
@[simp] theorem restrictR_apply {M N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (f : M.carrier →ₗ[(algebra A).carrierᵐᵒᵖ] N.carrier) (x : M.carrier) :
    restrictR f x = f x := rfl

/-- A graded homomorphism of unbundled differential graded modules, bundled. -/
abbrev bundleGradedHom {M N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : Stacks.DifferentialGraded.DGModule.GradedHom M N) :
    GradedHom (bundle hM) (bundle hN) where
  toFun := restrictR f.toFun
  map_smul x a := f.toFun.map_smul (MulOpposite.op a) x
  map_grading := f.map_grading

/-- A homomorphism of unbundled differential graded modules, bundled. -/
abbrev bundleHom {M N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : Stacks.DifferentialGraded.DGModule.Hom M N) :
    Hom (bundle hM) (bundle hN) where
  toFun := restrictR f.toFun
  map_smul x a := f.toFun.map_smul (MulOpposite.op a) x
  map_grading := f.map_grading
  map_d := LinearMap.ext f.commute_d

/-- An unbundled differential graded isomorphism is bijective. -/
theorem iso_bijective {M N : Stacks.DifferentialGraded.DGModule (algebra A)}
    (e : Stacks.DifferentialGraded.DGModule.Iso M N) : Function.Bijective e.toFun :=
  ⟨Function.LeftInverse.injective e.left_inv, Function.RightInverse.surjective e.right_inv⟩

/-- A lawful differential graded submodule of a lawful differential graded module is itself a
lawful differential graded module. -/
theorem dgSubmodule_isLawful {M : Stacks.DifferentialGraded.DGModule (algebra A)} (hM : M.IsLawful)
    (K : Stacks.DifferentialGraded.DGModule.DGSubmodule M) (hK : K.IsLawful) :
    K.toDGModule.IsLawful :=
  ⟨hK, fun n m x a hx ha => hM.grading_smul n m (x : K.toSubmodule).val a hx ha,
    fun n x hx => hM.d_mem n (x : K.toSubmodule).val hx,
    fun x => Subtype.ext (hM.d_comp_d (x : K.toSubmodule).val),
    fun n m x a hx ha => Subtype.ext (hM.leibniz n m (x : K.toSubmodule).val a hx ha)⟩

/-- The algebra, viewed as a module over itself, is lawful. -/
theorem free_isLawful {B : Stacks.DifferentialGraded.DGAlgebra R} (hB : B.IsLawful) :
    (Stacks.DifferentialGraded.DGModule.free B).IsLawful := by
  unfold Stacks.DifferentialGraded.DGModule.free
  refine ⟨DirectSum.Decomposition.isInternal B.grading, ?_, hB.d_mem, hB.d_comp_d, hB.leibniz⟩
  intro n m x a hx ha
  change x * a ∈ B.grading (n + m)
  exact SetLike.mul_mem_graded hx ha

/-- A shift of a lawful differential graded module is lawful. -/
theorem shift_isLawful {B : Stacks.DifferentialGraded.DGAlgebra R} (hB : B.IsLawful)
    {M : Stacks.DifferentialGraded.DGModule B} (hM : M.IsLawful) (k : ℤ) :
    (M.shift k).IsLawful := by
  rw [← DifferentialGraded.NativeCover.Native.ofModule_module M hB hM, ←
    DifferentialGraded.NativeCover.Native.ofModule_shift]
  exact DifferentialGraded.NativeCover.Native.ofModule_isLawful _

/-- A direct sum of lawful differential graded modules is lawful, provided its grading is
internal. -/
theorem directSum_isLawful {B : Stacks.DifferentialGraded.DGAlgebra R} {ι : Type*} [DecidableEq ι]
    (N : ι → Stacks.DifferentialGraded.DGModule B) (hN : ∀ i, (N i).IsLawful)
    (hint : DirectSum.IsInternal (Stacks.DifferentialGraded.DGModule.directSumGrading N)) :
    (Stacks.DifferentialGraded.DGModule.directSum N).IsLawful := by
  unfold Stacks.DifferentialGraded.DGModule.directSum
  refine ⟨hint, ?_, ?_, ?_, ?_⟩
  · intro n m x a hx ha i
    change ((MulOpposite.op a) • x) i ∈ (N i).grading (n + m)
    rw [DirectSum.smul_apply]
    exact (hN i).grading_smul n m (x i) a (hx i) ha
  · intro n x hx i
    rw [DifferentialGraded.NativeCover.Native.directSum_d_apply]
    exact (hN i).d_mem n (x i) (hx i)
  · intro x
    apply DirectSum.ext
    intro i
    simp only [DifferentialGraded.NativeCover.Native.directSum_d_apply, (hN i).d_comp_d,
      DirectSum.zero_apply]
  · intro n m x a hx ha
    apply DirectSum.ext
    intro i
    simp only [DifferentialGraded.NativeCover.Native.directSum_d_apply, DirectSum.smul_apply,
      DirectSum.add_apply]
    exact (hN i).leibniz n m (x i) a (hx i) ha

/-- A direct sum of shifts of the algebra is lawful. Internality of its grading is the
internality already proved for the generic shift sum of Tag 09KN. -/
theorem shiftSum_isLawful (A : DifferentialGradedAlgebra.{u, u} R)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    (Stacks.DifferentialGraded.DGModule.directSum
      (fun i => Stacks.DifferentialGraded.DGModule.shiftFree (algebra A) (k i))).IsLawful := by
  have hint : DirectSum.IsInternal (Stacks.DifferentialGraded.DGModule.directSumGrading
      (fun i => Stacks.DifferentialGraded.DGModule.shiftFree (algebra A) (k i))) :=
    (DifferentialGraded.NativeCover.Native.ofModule_isLawful (A := algebra A) (hA :=
      algebra_isLawful A)
      (DifferentialGraded.NativeCover.ShiftSum.shiftDG R A.A A.grading
        (DifferentialGraded.NativeCover.Native.algebra (algebra A) (algebra_isLawful A)) ι
          k)).isInternal
  exact directSum_isLawful _
    (fun i => shift_isLawful (algebra_isLawful A) (free_isLawful (algebra_isLawful A)) (k i)) hint

end Unbundled

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Direct sums of shifts -/

/-- The direct sum of shifts `⨁ i, A[k i]` of the algebra, as a bundled differential graded
`A`-module: the underlying right module is `⨁ i, A`, an element is homogeneous of degree `n`
exactly when its `i`-th component lies in `A^{n + k i}`, and the differential acts on the `i`-th
component by `(-1)^{|k i|} d_A`. -/
@[implicit_reducible]
def directSumShifts (A : DifferentialGradedAlgebra.{u, u} R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) : DifferentialGradedModule.{u, u, u} A :=
  Unbundled.bundle (Unbundled.shiftSum_isLawful A k)

/-- Membership in the degree-`n` piece of a direct sum of shifts is componentwise: `x` is
homogeneous of degree `n` exactly when `x i ∈ A^{n + k i}` for every cell `i`. -/
theorem mem_directSumShifts_grading {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (n : ℤ)
    (x : ⨁ _ : ι, A.A) :
    x ∈ (directSumShifts A k).grading n ↔ ∀ i, x i ∈ A.grading (n + k i) :=
  Iff.rfl

/-- The differential of a direct sum of shifts, on the `j`-th coprojection: it is the
differential of the algebra on that summand, carrying the sign of that summand's shift.

The module `N` must be pinned when applying `DirectSum.toModule_lof` here: left to be inferred
it is a metavariable when `Module R N` is demanded, and synthesis then fails rather than
postponing. -/
theorem directSumShifts_d_lof {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (j : ι) (x : A.A) :
    (directSumShifts A k).d (DirectSum.lof R ι (fun _ => A.A) j x)
      = DirectSum.lof R ι (fun _ => A.A) j (((-1 : ℤ) ^ (k j).natAbs) • A.d x) :=
  DirectSum.toModule_lof (R := R) (M := fun _ : ι => A.A) (N := (⨁ _ : ι, A.A)) j x

/-! ### Property (P) -/

/-- A *property-(P) filtration* of a differential graded `A`-module `P` (Tag 09KK): an
exhaustive increasing filtration `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯ ⊆ P` by differential graded
submodules whose inclusions are admissible monomorphisms and whose successive quotients are
direct sums of shifts of `A`.

The stages are presented by injective homomorphisms `ι i : F i ⟶ P` rather than as submodules,
and the graded pieces by surjective homomorphisms onto direct sums of shifts with the prescribed
kernel; the implicit stage `F_{-1} = 0` is encoded by the requirement that `F 0` itself be
isomorphic to a direct sum of shifts. -/
@[stacks_fixed 09KK "a filtration as in property (P): exhaustive, admissible inclusions, \
graded pieces direct sums of shifts A[k]; bundled encoding"]
structure PropertyPFiltration (P : DifferentialGradedModule.{u, u, u} A) where
  /-- The stages `F i` of the filtration. -/
  F : ℕ → DifferentialGradedModule.{u, u, u} A
  /-- The embedding of the `i`-th stage into the filtered module. -/
  ι : ∀ i, Hom (F i) P
  /-- Each stage embeds into the filtered module. -/
  injective : ∀ i, Function.Injective (ι i).toFun
  /-- The transition inclusion `F i ⟶ F (i + 1)`. -/
  incl : ∀ i, Hom (F i) (F (i + 1))
  /-- The transition inclusions are compatible with the embeddings into `P`. -/
  incl_comp : ∀ i x, (ι (i + 1)).toFun ((incl i).toFun x) = (ι i).toFun x
  /-- Property (P)(2): every transition inclusion is an admissible monomorphism. -/
  admissible : ∀ i, IsAdmissibleMono (incl i)
  /-- Property (P)(1): the filtration is exhaustive. -/
  exhaustive : ∀ x : P.M, ∃ i y, (ι i).toFun y = x
  /-- The cells of the bottom graded piece `F 0 / F_{-1} = F 0`. -/
  bottomIndex : Type u
  /-- Decidable equality of the bottom cells, needed to form their direct sum. -/
  bottomDecidableEq : DecidableEq bottomIndex
  /-- The shift attached to each bottom cell. -/
  bottomShift : bottomIndex → ℤ
  /-- Property (P)(3) for the bottom piece, as a homomorphism onto the direct sum of shifts. -/
  bottomMap : Hom (F 0) (@directSumShifts _ _ _ _ bottomDecidableEq bottomShift)
  /-- The bottom map is an isomorphism. -/
  bottom_bijective : Function.Bijective bottomMap.toFun
  /-- The cells of the `i`-th graded piece `F (i + 1) / F i`. -/
  quotientIndex : ℕ → Type u
  /-- Decidable equality of the cells of each graded piece. -/
  quotientDecidableEq : ∀ i, DecidableEq (quotientIndex i)
  /-- The shift attached to each cell of the `i`-th graded piece. -/
  quotientShift : ∀ i, quotientIndex i → ℤ
  /-- Property (P)(3): the projection of `F (i + 1)` onto its `i`-th graded piece. -/
  quotientMap : ∀ i, Hom (F (i + 1))
    (@directSumShifts _ _ _ _ (quotientDecidableEq i) (quotientShift i))
  /-- The projection onto the `i`-th graded piece is surjective. -/
  quotient_surjective : ∀ i, Function.Surjective (quotientMap i).toFun
  /-- Its kernel is the previous stage, so the graded piece really is `F (i + 1) / F i`. -/
  quotient_ker : ∀ i, LinearMap.ker (quotientMap i).toFun = LinearMap.range (incl i).toFun

add_to_stacks 09KK "a filtration as in property (P); unbundled encoding"
  Stacks.DifferentialGraded.DGModule.PropertyPFiltration

namespace PropertyPFiltration

variable {P : DifferentialGradedModule.{u, u, u} A} (F : PropertyPFiltration P)

/-- The transition inclusions of a property-(P) filtration are injective. -/
theorem incl_injective (i : ℕ) : Function.Injective (F.incl i).toFun :=
  (F.admissible i).injective

/-- An element of the `(i + 1)`-st stage dies in the `i`-th graded piece exactly when it comes
from the `i`-th stage. -/
theorem quotientMap_eq_zero_iff (i : ℕ) (x : (F.F (i + 1)).M) :
    (F.quotientMap i).toFun x = 0 ↔ ∃ y, (F.incl i).toFun y = x := by
  rw [← LinearMap.mem_ker, F.quotient_ker i, LinearMap.mem_range]

/-- The bottom stage `F 0` of a property-(P) filtration *is* a direct sum of shifts of `A`. -/
def bottomEquiv :
    (F.F 0).M ≃ₗ[R]
      (@directSumShifts R _ A F.bottomIndex F.bottomDecidableEq F.bottomShift).M :=
  LinearEquiv.ofBijective F.bottomMap.toFun F.bottom_bijective

/-- The projection of `F (i + 1)` onto the `i`-th graded piece, descended to the quotient by the
previous stage. -/
def quotientLift (i : ℕ) :
    ((F.F (i + 1)).M ⧸ LinearMap.range (F.incl i).toFun) →ₗ[R]
      (@directSumShifts R _ A (F.quotientIndex i) (F.quotientDecidableEq i)
        (F.quotientShift i)).M :=
  (LinearMap.range (F.incl i).toFun).liftQ (F.quotientMap i).toFun (F.quotient_ker i).ge

/-- The `i`-th graded piece `F (i + 1) / F i` of a property-(P) filtration *is* a direct sum of
shifts of `A`. This is the form in which the successive quotients are consumed. -/
def quotientEquiv (i : ℕ) :
    ((F.F (i + 1)).M ⧸ LinearMap.range (F.incl i).toFun) ≃ₗ[R]
      (@directSumShifts R _ A (F.quotientIndex i) (F.quotientDecidableEq i)
        (F.quotientShift i)).M :=
  LinearEquiv.ofBijective (F.quotientLift i)
    ⟨LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ (F.quotient_ker i).le),
      LinearMap.range_eq_top.1 ((Submodule.range_liftQ _ _ _).trans
        (LinearMap.range_eq_top.2 (F.quotient_surjective i)))⟩

/-- **Each step of a property-(P) filtration is admissible short exact.** The inclusion
`F i ⟶ F (i + 1)` and the projection of `F (i + 1)` onto its `i`-th graded piece form a short
exact sequence that is split as a sequence of graded modules.

Four of the five conditions are the filtration's own data. The content is the graded section of
the projection: a graded retraction `r` of the inclusion makes `x ↦ x - incl (r x)` vanish on
the image of `F i`, hence on the kernel of the projection, so it descends along the projection
to a map `s` with `s (q x) = x - incl (r x)`; this `s` is a section of `q` because
`incl (r x)` lies in the kernel of `q`, and it is graded because `q`, being surjective and
degree-preserving, is already surjective on each homogeneous piece. -/
theorem isAdmissibleShortExact_incl_quotientMap (i : ℕ) :
    IsAdmissibleShortExact (F.incl i) (F.quotientMap i) := by
  obtain ⟨r, hr⟩ := F.admissible i
  have hsurj : Function.Surjective (F.quotientMap i).toFun := F.quotient_surjective i
  have hker : LinearMap.ker (F.quotientMap i).toFun ≤
      LinearMap.ker (LinearMap.id - (F.incl i).toFun ∘ₗ r.toFun) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (F.quotientMap_eq_zero_iff i x).1 hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_coe, id_eq,
      LinearMap.comp_apply, hr y, sub_self]
  obtain ⟨s, hs⟩ : ∃ s : (@directSumShifts R _ A (F.quotientIndex i) (F.quotientDecidableEq i)
      (F.quotientShift i)).M →ₗ[R] (F.F (i + 1)).M, ∀ x : (F.F (i + 1)).M,
        s ((F.quotientMap i).toFun x) = x - (F.incl i).toFun (r.toFun x) := by
    refine ⟨(LinearMap.ker (F.quotientMap i).toFun).liftQ
        (LinearMap.id - (F.incl i).toFun ∘ₗ r.toFun) hker ∘ₗ
      ((F.quotientMap i).toFun.quotKerEquivOfSurjective hsurj).symm.toLinearMap, fun x => ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearMap.comp_apply]
  have hzero : ∀ x : (F.F (i + 1)).M,
      (F.quotientMap i).toFun ((F.incl i).toFun (r.toFun x)) = 0 := by
    intro x
    exact (F.quotientMap_eq_zero_iff i _).2 ⟨r.toFun x, rfl⟩
  refine { injective := F.incl_injective i
           surjective := hsurj
           exact := (F.quotient_ker i).symm
           admissibleMono := F.admissible i
           admissibleEpi := ⟨{ toFun := s, map_smul := ?_, map_grading := ?_ }, ?_⟩ }
  · intro z a
    obtain ⟨x, rfl⟩ := hsurj z
    rw [← (F.quotientMap i).map_smul, hs, hs, r.map_smul, (F.incl i).map_smul, smul_sub]
  · intro n z hz
    obtain ⟨x, hx, rfl⟩ := Hom.exists_mem_grading_of_surjective hsurj hz
    rw [hs]
    exact ((F.F (i + 1)).grading n).sub_mem hx
      ((F.incl i).map_grading n _ (r.map_grading n x hx))
  · intro z
    obtain ⟨x, rfl⟩ := hsurj z
    rw [hs, map_sub, hzero, sub_zero]

end PropertyPFiltration

/-! ### Quasi-isomorphisms -/

/-- The cycle-and-boundary criterion for a homomorphism of differential graded modules to be a
quasi-isomorphism: in every degree, every cocycle of the target is congruent modulo a boundary
to the image of a cocycle of the source, and a cocycle of the source whose image is a boundary
is itself a boundary. -/
def IsQuasiIsomorphism {M N : DifferentialGradedModule.{u, u, u} A} (f : Hom M N) : Prop :=
  ∀ n : ℤ,
    (∀ y : N.M, y ∈ N.grading n → N.d y = 0 →
      ∃ x : M.M, x ∈ M.grading n ∧ M.d x = 0 ∧
        ∃ z : N.M, z ∈ N.grading (n - 1) ∧ N.d z = y - f.toFun x) ∧
    (∀ x : M.M, x ∈ M.grading n → M.d x = 0 →
      (∃ z : N.M, z ∈ N.grading (n - 1) ∧ N.d z = f.toFun x) →
        ∃ z : M.M, z ∈ M.grading (n - 1) ∧ M.d z = x)

/-- A map induced on quotients by `Submodule.mapQ` is bijective as soon as it hits every class of
the target and reflects membership in the subgroup divided out. -/
private theorem mapQ_bijective {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {p : Submodule R X} {q : Submodule R Y} (g : X →ₗ[R] Y)
    (h : p ≤ q.comap g) (hs : ∀ y : Y, ∃ x : X, g x - y ∈ q)
    (hi : ∀ x : X, g x ∈ q → x ∈ p) :
    Function.Bijective (Submodule.mapQ p q g h) := by
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective p a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective p b
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    exact (Submodule.Quotient.eq p).2 (hi (a - b) (by rwa [map_sub]))
  · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective q c
    obtain ⟨x, hx⟩ := hs c
    exact ⟨Submodule.Quotient.mk x, by rwa [Submodule.mapQ_apply, Submodule.Quotient.eq]⟩

/-- The forgetful functor to cochain complexes is `toCochainComplex` on objects.

Needed as a rewrite rule: the simp lemmas of `toCochainComplex` are keyed on
`toCochainComplex` itself, so they do not fire against the syntactically different
`(forgetToCochainComplex A).obj M`, even though the two are equal by definition. -/
private theorem forget_obj (M : DifferentialGradedModule.{u, u, u} A) :
    (forgetToCochainComplex A).obj M = M.toCochainComplex := rfl

/-- The forgetful functor to cochain complexes is `Hom.toCochainMap` on morphisms, as a rewrite
rule; see `forget_obj`. -/
private theorem forget_map {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N) :
    (forgetToCochainComplex A).map f = f.toCochainMap := rfl


/-- A morphism of short complexes of modules is a quasi-isomorphism as soon as the
cycle-and-boundary criterion holds: every cycle of the target is the image of a cycle of the
source modulo a boundary, and a cycle of the source whose image is a boundary is a boundary.

The criterion is checked against the explicit left homology data of a short complex of modules,
for which the homology object is literally `ker g / range f`. -/
private theorem shortComplex_quasiIso_of_criterion
    {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g.hom y = 0 →
      ∃ x : S.X₂, S.g.hom x = 0 ∧ ∃ w : T.X₁, T.f.hom w = φ.τ₂.hom x - y)
    (hinj : ∀ x : S.X₂, S.g.hom x = 0 →
      (∃ w : T.X₁, T.f.hom w = φ.τ₂.hom x) → ∃ v : S.X₁, S.f.hom v = x) :
    ShortComplex.QuasiIso φ := by
  have hcomm : ∀ x : S.X₂, T.g.hom (φ.τ₂.hom x) = φ.τ₃.hom (S.g.hom x) := by
    intro x
    simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp φ.comm₂₃) x
  have hcommf : ∀ v : S.X₁, T.f.hom (φ.τ₁.hom v) = φ.τ₂.hom (S.f.hom v) := by
    intro v
    simpa using LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp φ.comm₁₂) v
  have hKmem : ∀ x : LinearMap.ker S.g.hom,
      φ.τ₂.hom (x : S.X₂) ∈ LinearMap.ker T.g.hom := by
    intro x
    rw [LinearMap.mem_ker, hcomm, show S.g.hom (x : S.X₂) = 0 from x.2, map_zero]
  let φKmap : ↥(LinearMap.ker S.g.hom) →ₗ[R] ↥(LinearMap.ker T.g.hom) :=
    (φ.τ₂.hom ∘ₗ (LinearMap.ker S.g.hom).subtype).codRestrict _ (fun x => hKmem x)
  have hφKrange : LinearMap.range S.moduleCatToCycles ≤
      Submodule.comap φKmap (LinearMap.range T.moduleCatToCycles) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨φ.τ₁.hom v, Subtype.ext (hcommf v)⟩
  let γ : ShortComplex.LeftHomologyMapData φ
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData :=
    { φK := ModuleCat.ofHom φKmap
      φH := ModuleCat.ofHom (Submodule.mapQ _ _ φKmap hφKrange)
      commi := by ext x; rfl
      commf' := by ext v; exact Subtype.ext (hcommf v).symm
      commπ := by ext x; rfl }
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (Submodule.mapQ _ _ φKmap hφKrange)
  refine mapQ_bijective _ _ (fun y => ?_) (fun x hx => ?_)
  · obtain ⟨x, hx, w, hw⟩ := hsurj (y : T.X₂) y.2
    exact ⟨⟨x, hx⟩, ⟨w, Subtype.ext hw⟩⟩
  · obtain ⟨w, hw⟩ := hx
    obtain ⟨v, hv⟩ := hinj (x : S.X₂) x.2 ⟨w, congrArg Subtype.val hw⟩
    exact ⟨v, Subtype.ext hv⟩

/-- The short complex `X^m ⟶ X^{m+1} ⟶ X^{m+2}` of modules underlying a differential graded
module `X`. -/
private abbrev forgetShortComplex (X : DifferentialGradedModule.{u, u, u} A) (m : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℤ) m (m + 1)
    (m + 1 + 1)).obj ((forgetToCochainComplex A).obj X)

/-- An element of `X^{m+1}` is killed by the second map of `forgetShortComplex X m` exactly when
it is a cocycle. -/
private theorem forget_g_eq_zero_iff {X : DifferentialGradedModule.{u, u, u} A}
    {m : ℤ} (x : (forgetShortComplex X m).X₂) :
    (forgetShortComplex X m).g.hom x = 0 ↔ X.d x.1 = 0 := by
  refine Subtype.ext_iff.trans ?_
  simp only [forget_obj, HomologicalComplex.shortComplexFunctor'_obj_g, toCochainComplex_d]
  rfl

/-- The first map of `forgetShortComplex X m` sends `w` to `u` exactly when `d w = u`. -/
private theorem forget_f_eq_iff {X : DifferentialGradedModule.{u, u, u} A} {m : ℤ}
    {w : (forgetShortComplex X m).X₁} {u : (forgetShortComplex X m).X₂} :
    (forgetShortComplex X m).f.hom w = u ↔ X.d w.1 = u.1 := by
  refine Subtype.ext_iff.trans ?_
  simp only [forget_obj, HomologicalComplex.shortComplexFunctor'_obj_f, toCochainComplex_d]
  rfl

/-- The cycle-and-boundary criterion implies that the underlying cochain map of a homomorphism
of differential graded modules is a quasi-isomorphism in the sense of Mathlib. -/
theorem quasiIso_of_isQuasiIsomorphism {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N)
    (hf : IsQuasiIsomorphism f) : QuasiIso ((forgetToCochainComplex A).map f) := by
  rw [quasiIso_iff]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  rw [quasiIsoAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp)]
  refine shortComplex_quasiIso_of_criterion _ (fun y hy => ?_) (fun x hx hb => ?_)
  · obtain ⟨x, hx, hdx, z, hz, hzeq⟩ :=
      (hf (m + 1)).1 y.1 y.2 ((forget_g_eq_zero_iff y).1 hy)
    refine ⟨⟨x, hx⟩, (forget_g_eq_zero_iff (X := M) ⟨x, hx⟩).2 hdx,
      ⟨-z, by simpa using neg_mem hz⟩, forget_f_eq_iff.2 ?_⟩
    rw [map_neg, hzeq, neg_sub]
    rfl
  · obtain ⟨w, hw⟩ := hb
    obtain ⟨z, hz, hzeq⟩ := (hf (m + 1)).2 x.1 x.2 ((forget_g_eq_zero_iff x).1 hx)
      ⟨w.1, by simpa using w.2, forget_f_eq_iff.1 hw⟩
    exact ⟨⟨z, by simpa using hz⟩, forget_f_eq_iff.2 hzeq⟩

/-! ### Existence of property-(P) resolutions -/

/-- The property-(P) filtration produced by the unbundled development, bundled. -/
public def bundleFiltration {P : Stacks.DifferentialGraded.DGModule (Unbundled.algebra A)}
    (hP : P.IsLawful)
    (F : Stacks.DifferentialGraded.DGModule.PropertyPFiltration P) :
    PropertyPFiltration (Unbundled.bundle hP) := by
  let hF := fun i => Unbundled.dgSubmodule_isLawful hP (F.F i) (F.F_lawful i)
  letI := F.bottomShiftIndexDec
  let hB := Unbundled.shiftSum_isLawful A F.bottomShiftAmount
  let hQ := fun i => @Unbundled.shiftSum_isLawful R _ A (F.shiftIndex i) (F.shiftIndexDec i)
    (F.shiftAmount i)
  choose q hs hk using F.isQuotient
  refine {
    F := fun i => Unbundled.bundle (hF i)
    ι := fun i => Unbundled.bundleHom (hF i) hP (F.F i).incl
    injective := fun _ => Subtype.val_injective
    incl := fun i => Unbundled.bundleHom (hF i) (hF (i + 1)) (F.inclHom i)
    incl_comp := F.inclHom_apply
    admissible := ?_
    exhaustive := ?_
    bottomIndex := F.bottomShiftIndex
    bottomDecidableEq := F.bottomShiftIndexDec
    bottomShift := F.bottomShiftAmount
    bottomMap := Unbundled.bundleHom (hF 0) hB F.bottomIso.toHom
    bottom_bijective := Unbundled.iso_bijective F.bottomIso
    quotientIndex := F.shiftIndex
    quotientDecidableEq := F.shiftIndexDec
    quotientShift := F.shiftAmount
    quotientMap := fun i =>
      Unbundled.bundleHom (hF (i + 1)) (hQ i) ((F.quotientIso i).toHom.comp (q i))
    quotient_surjective := fun i =>
      (Unbundled.iso_bijective (F.quotientIso i)).surjective.comp (hs i)
    quotient_ker := ?_ }
  · intro i
    obtain ⟨_, r, hr⟩ := F.admissible i
    exact ⟨Unbundled.bundleGradedHom (hF (i + 1)) (hF i) r, hr⟩
  · intro x
    obtain ⟨i, hi⟩ := F.exhaustive x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i
    ext x
    change (F.quotientIso i).toFun ((q i).toFun x) = 0 ↔ ∃ y, (F.inclHom i).toFun y = x
    rw [← map_zero (F.quotientIso i).toFun,
      (Unbundled.iso_bijective (F.quotientIso i)).injective.eq_iff]
    exact SetLike.ext_iff.mp (hk i) x

/-- **Property-(P) resolutions exist** (Tag 09KP). Every right differential graded module `M`
over a differential graded algebra `(A, d)` receives a quasi-isomorphism from a differential
graded `A`-module `P` carrying a property-(P) filtration: an exhaustive increasing filtration by
differential graded submodules with admissible inclusions whose successive quotients are direct
sums of shifts of `A`. -/
@[stacks 09KP]
theorem exists_propertyP_resolution (A : DifferentialGradedAlgebra.{u, u} R)
    (M : DifferentialGradedModule.{u, u, u} A) :
    ∃ (P : DifferentialGradedModule.{u, u, u} A) (f : P ⟶ M),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ Nonempty (PropertyPFiltration P) := by
  obtain ⟨P, hP, f, hf, ⟨F⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  let e : Hom (Unbundled.bundle hP) M :=
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f.toFun
      map_smul := fun x a => f.toFun.map_smul (MulOpposite.op a) x
      map_grading := f.map_grading
      map_d := LinearMap.ext f.commute_d }
  exact ⟨Unbundled.bundle hP, e, quasiIso_of_isQuasiIsomorphism e hf, ⟨bundleFiltration hP F⟩⟩

end DifferentialGradedModule

end
