module

public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Finite and integral ring extensions

This file contains two results on how a ring map interacts with finiteness of modules over it and
with integrality.

The first concerns a ring map `R → S` which is finite (`S` is generated as an `R`-module by
finitely many elements) and finitely presented as a ring map (`S` is a quotient of a polynomial
ring in finitely many variables over `R` by a finitely generated ideal). For `M` an `S`-module,
viewed as an `R`-module by restriction of scalars, `M` is finitely presented over `R` if and only
if it is finitely presented over `S`. Together the two hypotheses say precisely that `S` is a
finitely presented `R`-module, and that is all that is used: for `←`, a presentation of `S` over
`R` is spliced into a presentation `S^{⊕m} → S^{⊕n} → M → 0` over `S`; for `→`, the module `M` is
a quotient of the base change `S ⊗[R] M`, which is finitely presented over `S`, and the kernel of
`S ⊗[R] M → M` is finitely generated already as an `R`-submodule because `S ⊗[R] M` is a finite
`R`-module.

The second concerns a finite family of ring maps `R i → S i`. An element of the product `∏ i, S i`
is integral over `∏ i, R i` exactly when each of its components is integral over the corresponding
`R i` — this is `isIntegral_pi_iff`, [StacksProject 0CY8] — so the integral closure of `∏ i, R i`
in `∏ i, S i` is the product of the integral closures of the `R i` in the `S i`; in particular
`∏ i, R i → ∏ i, S i` is integrally closed if and only if each `R i → S i` is.

## Main results

* `Module.FinitePresentation.restrictScalars_iff`: for `R → S` finite and finitely presented as
  a ring map and `M` an `S`-module,
  `Module.FinitePresentation R M ↔ Module.FinitePresentation S M`.
* `IsIntegralClosure.pi_iff`: for a finite index type, `∏ i, S' i` is the integral closure of
  `∏ i, R i` in `∏ i, S i` if and only if `S' i` is the integral closure of `R i` in `S i`
  for every `i`.

## Implementation notes

"Finite and finitely presented ring map `R → S`" is spelled as the two instance hypotheses
`Module.Finite R S` and `Algebra.FinitePresentation R S`, whose conjunction is equivalent to the
single hypothesis `Module.FinitePresentation R S` by
`Module.FinitePresentation.iff_finitePresentation_of_finite`. The pair is chosen because instance
resolution derives it from `Module.FinitePresentation R S` automatically, whereas the converse
derivation is a lemma the caller would have to apply by hand.

The `R`-module structure on `M` is not `RestrictScalars R S M` but a second `Module R M` instance
tied to the `S`-action by `IsScalarTower R S M`, the standard spelling for a module over a tower;
the name follows the sibling `Submodule.FG.restrictScalars_iff`, an equivalence of the same shape
under the same finiteness hypothesis on `R → S`.

Integral closure is spelled with `IsIntegralClosure S' R S` — the algebra map `S' → S` is
injective with range the set of elements of `S` integral over `R` — rather than with the
construction `integralClosure R S : Subalgebra R S`, because `∏ i, S' i` is not a subalgebra of
`∏ i, S i` over `∏ i, R i` in the sense of `Subalgebra.pi`, which takes a *constant* base ring.
The literal statement about integral closures is the specialisation
`S' i = integralClosure (R i) (S i)`, which the `←` direction gives from
`integralClosure.isIntegralClosure`, and the "in particular" is the same `Iff` at `S' = R`: the
product algebra structure of `∀ i, R i` over itself is the identity, so both sides read as
`IsIntegrallyClosedIn`.

`Finite ι` is used only by the `←` direction, and there it is essential: over an infinite index
the conclusion fails, for instance for `R i = ℤ`, `S i = ℤ[X] / (X ^ i - 2)` and `x i` the class
of `X`, whose degrees of integrality are unbounded. An empty index type is allowed.

## References

* [StacksProject 0561](https://stacks.math.columbia.edu/tag/0561)
* [StacksProject 0564](https://stacks.math.columbia.edu/tag/0564)
* [StacksProject 0CY8](https://stacks.math.columbia.edu/tag/0CY8)
* [StacksProject 0CY9](https://stacks.math.columbia.edu/tag/0CY9)
-/

namespace Module.FinitePresentation

open TensorProduct in
/-- The finite case of **Stacks 0561**: if `S` is a finite `R`-algebra and `M` is an `S`-module
which is finitely presented as an `R`-module, then `M` is finitely presented as an `S`-module.

Compare `Module.Finite.of_restrictScalars_finite`, which needs no hypothesis on `R → S`. -/
private theorem of_restrictScalars_finitePresentation (R S M : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R S] [Module.FinitePresentation R M] : Module.FinitePresentation S M := by
  -- `M` is a quotient of `S ⊗[R] M`, a finite `R`-module since `S` and `M` are, so the kernel is
  -- finitely generated already as an `R`-submodule.
  let f : S ⊗[R] M →ₗ[S] M := LinearMap.liftBaseChange S .id
  have hf : Function.Surjective f := fun m ↦ ⟨1 ⊗ₜ m, by simp [f]⟩
  exact Module.finitePresentation_of_surjective f hf
    (.of_restrictScalars R (Module.FinitePresentation.fg_ker (R := R) (f.restrictScalars R) hf))

@[expose] public section

/-- **Stacks 0564.** Let `R → S` be a finite and finitely presented ring map and let `M` be an
`S`-module, regarded as an `R`-module by restriction of scalars. Then `M` is finitely presented
as an `R`-module if and only if `M` is finitely presented as an `S`-module. -/
@[stacks 0564]
public theorem restrictScalars_iff (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M :=
  have : Module.FinitePresentation R S := .of_finite_of_finitePresentation R S
  ⟨fun _ ↦ of_restrictScalars_finitePresentation R S M, fun _ ↦ .trans R M S⟩
end

end Module.FinitePresentation

/-- A family of predicates, each holding at `0`, holds at every coordinate of `Pi.single i x` if
and only if it holds at `x`. -/
private theorem forall_pi_single_iff {ι : Type*} [DecidableEq ι] {B : ι → Type*}
    [∀ i, Zero (B i)] {P : ∀ i, B i → Prop} (h0 : ∀ i, P i 0) {i : ι} (x : B i) :
    (∀ j, P j (Pi.single i x j)) ↔ P i x := by
  refine ⟨fun h ↦ by simpa using h i, fun h j ↦ ?_⟩
  rcases eq_or_ne j i with rfl | hj
  · simpa
  · simpa [Pi.single_eq_of_ne hj] using h0 j

section Pi

variable {ι : Type*} {A B : ι → Type*} [∀ i, CommSemiring (A i)] [∀ i, Semiring (B i)]
  [∀ i, Algebra (A i) (B i)]

/-- The structure map of a product algebra is injective if and only if each of its components
is. -/
private theorem injective_algebraMap_pi_iff :
    Function.Injective (algebraMap (∀ i, A i) (∀ i, B i)) ↔
      ∀ i, Function.Injective (algebraMap (A i) (B i)) := by
  have h : ⇑(algebraMap (∀ i, A i) (∀ i, B i)) = Pi.map fun i ↦ ⇑(algebraMap (A i) (B i)) := by
    ext y i
    rw [Pi.map_apply, algebraMap_pi_apply]
  rw [h, Pi.map_injective]

/-- An element of a product algebra lies in the range of the structure map if and only if each of
its components does. -/
private theorem exists_algebraMap_pi_eq_iff (x : ∀ i, B i) :
    (∃ y : ∀ i, A i, algebraMap (∀ i, A i) (∀ i, B i) y = x) ↔
      ∀ i, ∃ y : A i, algebraMap (A i) (B i) y = x i := by
  simp only [funext_iff, algebraMap_pi_apply]
  exact (Classical.skolem (p := fun i y ↦ algebraMap (A i) (B i) y = x i)).symm

/-- An element of `∏ i, B i` supported at a single index `i` lies in the range of the structure
map if and only if its `i`-th coordinate lies in the range of `algebraMap (A i) (B i)`. -/
private theorem exists_algebraMap_eq_pi_single_iff [DecidableEq ι] {i : ι} (x : B i) :
    (∃ y : ∀ j, A j, algebraMap (∀ j, A j) (∀ j, B j) y = Pi.single i x) ↔
      ∃ y : A i, algebraMap (A i) (B i) y = x := by
  rw [exists_algebraMap_pi_eq_iff]
  exact forall_pi_single_iff (P := fun j z ↦ ∃ y : A j, algebraMap (A j) (B j) y = z)
    (fun j ↦ ⟨0, map_zero _⟩) x

end Pi

/-- An element of `∏ i, S i` supported at a single index `i` is integral over `∏ i, R i` if and
only if its `i`-th coordinate is integral over `R i`. -/
private theorem isIntegral_pi_single_iff {ι : Type*} [Finite ι] [DecidableEq ι] {R S : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)] {i : ι} {x : S i} :
    IsIntegral (∀ j, R j) (Pi.single i x) ↔ IsIntegral (R i) x := by
  rw [isIntegral_pi_iff]
  exact forall_pi_single_iff (fun _ ↦ isIntegral_zero) x

@[expose] public section

/-- **Stacks 0CY9.** Let `R i → S i` be a finite family of ring maps and let `S' i` be an algebra
whose canonical map to `S i` identifies it with the integral closure of `R i` in `S i`. Then
`∏ i, S' i` is the integral closure of `∏ i, R i` in `∏ i, S i`, and conversely. Taking
`S' = R` this says that `∏ i, R i → ∏ i, S i` is integrally closed if and only if each
`R i → S i` is. -/
@[stacks 0CY9]
public theorem IsIntegralClosure.pi_iff {ι : Type*} [Finite ι] {R S S' : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, CommSemiring (S' i)]
    [∀ i, Algebra (R i) (S i)] [∀ i, Algebra (S' i) (S i)] :
    IsIntegralClosure (∀ i, S' i) (∀ i, R i) (∀ i, S i) ↔
      ∀ i, IsIntegralClosure (S' i) (R i) (S i) := by
  classical
  constructor
  · -- Test the product statement on the element of `∏ j, S j` supported at the index `i`.
    refine fun H i ↦ ⟨injective_algebraMap_pi_iff.1 H.algebraMap_injective i, fun {x} ↦ ?_⟩
    exact (isIntegral_pi_single_iff (R := R)).symm.trans
      (H.isIntegral_iff.trans (exists_algebraMap_eq_pi_single_iff (A := S') x))
  · refine fun H ↦ ⟨injective_algebraMap_pi_iff.2 fun i ↦ (H i).algebraMap_injective,
      fun {x} ↦ ?_⟩
    rw [isIntegral_pi_iff, exists_algebraMap_pi_eq_iff x]
    exact forall_congr' fun i ↦ (H i).isIntegral_iff

/-- The integral closure of `∏ i, R i` in `∏ i, S i` is `∏ i, S' i` as soon as each `S' i` is the
integral closure of `R i` in `S i`. -/
instance IsIntegralClosure.pi {ι : Type*} [Finite ι] {R S S' : ι → Type*}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, CommSemiring (S' i)]
    [∀ i, Algebra (R i) (S i)] [∀ i, Algebra (S' i) (S i)]
    [∀ i, IsIntegralClosure (S' i) (R i) (S i)] :
    IsIntegralClosure (∀ i, S' i) (∀ i, R i) (∀ i, S i) :=
  IsIntegralClosure.pi_iff.2 inferInstance
end

/-!
# Transitivity of integral closure

All rings here are commutative with unit and all ring maps are unital. Fix two
ring maps `A --f--> B --g--> C`.

An element `s` of `S` is *integral* over `R` with respect to a ring map
`φ : R → S` if there is a monic `p = X^n + c_{n-1} X^{n-1} + ⋯ + c_0` in `R[X]`
with `n ≥ 1` such that `s^n + φ(c_{n-1}) s^{n-1} + ⋯ + φ(c_0) = 0` in `S`; this is
Mathlib's `RingHom.IsIntegralElem`. The *integral closure* of `R` in `S` is the
subring `{ s ∈ S | s` is integral over `R }`.

Write

* `B'` for the integral closure of `A` in `B` along `f`, a subring of `B`;
* `C'` for the integral closure of `B'` in `C` along the restriction
  `B' ↪ B --g--> C`, a subring of `C`;
* `D` for the integral closure of `A` in `C` along `g ∘ f`, a subring of `C`.

Then `C' = D` as subrings of `C`, which is the conjunction of two inclusions: every
`c ∈ C` integral over `B'` is integral over `A`, and conversely.

## Main results

* `integral_closure_transitive`: `C' = D`.
* `Cprime_le_Dsub`: the inclusion `C' ⊆ D`, which carries the content — it is
  transitivity of integrality along the tower `A → B' → C`.
* `Dsub_le_Cprime`: the reverse inclusion, by pushing a witnessing monic
  polynomial from `A[X]` to `B'[X]`.

## Implementation notes

The three closures are packaged as `Bprime`, `Cprime` and `Dsub`, all instances of
`intClosureSubring`, which turns `integralClosure` into a `Subring` of the target
for a bare ring map rather than for an `Algebra` instance. Membership is unfolded
by `mem_intClosureSubring`.
-/

@[expose] public section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The integral closure of `A` in `B` with respect to a ring map `f : A → B`,
realized as a subring of `B`. An element `b : B` lies in this subring iff it is
integral over `A` (i.e. `f.IsIntegralElem b`); see `mem_intClosureSubring`. -/
@[ega "III 4.3.5" "more general"]
noncomputable def intClosureSubring (f : A →+* B) : Subring B :=
  letI := f.toAlgebra
  (integralClosure A B).toSubring

/-- Characterization of membership in `intClosureSubring`: `b` belongs to the
integral closure of `A` in `B` iff `b` is integral over `A` w.r.t. `f`. -/
theorem mem_intClosureSubring (f : A →+* B) (b : B) :
    b ∈ intClosureSubring f ↔ f.IsIntegralElem b := by
  unfold intClosureSubring
  let := f.toAlgebra
  rw [Subalgebra.mem_toSubring, mem_integralClosure_iff]
  rfl

/-- `B'`: the integral closure of `A` in `B` w.r.t. `f : A → B`. -/
@[ega "III 4.3.5" "more general"]
noncomputable def Bprime (f : A →+* B) : Subring B := intClosureSubring f

/-- `C'`: the integral closure of `B'` in `C` w.r.t. the restriction of
`g : B → C` to the subring `B'` (i.e. `g ∘ (B'.subtype)`). -/
noncomputable def Cprime (f : A →+* B) (g : B →+* C) : Subring C :=
  intClosureSubring (g.comp (Bprime f).subtype)

/-- `D`: the integral closure of `A` in `C` w.r.t. the composite `g ∘ f`. -/
noncomputable def Dsub (f : A →+* B) (g : B →+* C) : Subring C :=
  intClosureSubring (g.comp f)

/-- `f a` is always integral over `A`, so it lies in `B'`. -/
theorem mem_Bprime_of_apply (f : A →+* B) (a : A) : f a ∈ Bprime f := by
  rw [Bprime, mem_intClosureSubring]
  exact f.isIntegralElem_map

/-- Corestriction of `f : A →+* B` to its integral closure `B'`. -/
noncomputable def fCorestrict (f : A →+* B) : A →+* Bprime f :=
  f.codRestrict (Bprime f).toSubsemiring (mem_Bprime_of_apply f)

/-- Composing `fCorestrict f` with the inclusion of `Bprime f` into `B` recovers `f`. -/
@[simp] theorem fCorestrict_subtype (f : A →+* B) :
    (Bprime f).subtype.comp (fCorestrict f) = f :=
  RingHom.ext fun _ ↦ rfl

/-- Inclusion (1) `C' ⊆ D` (the substantive direction): every `c ∈ C` that is
integral over `B'` is integral over `A`. -/
theorem Cprime_le_Dsub (f : A →+* B) (g : B →+* C) :
    Cprime f g ≤ Dsub f g := by
  intro c hc
  rw [Cprime, mem_intClosureSubring] at hc
  rw [Dsub, mem_intClosureSubring, ← fCorestrict_subtype f, ← RingHom.comp_assoc]
  -- The tower `A → B' → C`, along `fCorestrict f` and `g ∘ B'.subtype`.
  algebraize_only [fCorestrict f, g.comp (Bprime f).subtype,
    (g.comp (Bprime f).subtype).comp (fCorestrict f)]
  -- `B'` is integral over `A`, since its inclusion into `B` is injective.
  have : Algebra.IsIntegral A (Bprime f) := ⟨fun b ↦ by
    unfold IsIntegral
    refine .of_map (f := fCorestrict f) (Bprime f).subtype_injective ?_
    rw [fCorestrict_subtype, Subring.subtype_apply, ← mem_intClosureSubring, ← Bprime]
    exact b.2⟩
  -- Transitivity of integrality along `A → B' → C`.
  exact isIntegral_trans (R := A) c hc

/-- Inclusion (2) `D ⊆ C'` (the easy direction): every `c ∈ C` that is integral
over `A` is integral over `B'`. -/
theorem Dsub_le_Cprime (f : A →+* B) (g : B →+* C) :
    Dsub f g ≤ Cprime f g := by
  intro c hc
  rw [Dsub, mem_intClosureSubring] at hc
  rw [Cprime, mem_intClosureSubring]
  exact .of_comp (f := fCorestrict f) (by rwa [RingHom.comp_assoc, fCorestrict_subtype])

/-- Stacks Tag 0308 (transitivity of integral closure): the integral closure of
`B'` in `C` equals the integral closure of `A` in `C`, as subrings of `C`. -/
@[stacks 0308]
theorem integral_closure_transitive (f : A →+* B) (g : B →+* C) :
    Cprime f g = Dsub f g :=
  le_antisymm (Cprime_le_Dsub f g) (Dsub_le_Cprime f g)

-- The former @[stacks 00PQ] declaration is now the Mathlib theorem, which reads the relation
-- as a polynomial and scales by its leading coefficient; the degenerate case `a n = 0` is
-- `RingHom.isIntegralElem_zero`.
add_to_stacks 00PQ "scaling by the leading coefficient makes an element integral"
  RingHom.isIntegralElem_leadingCoeff_mul
add_to_stacks 00PQ "the degenerate case, where the top coefficient vanishes"
  RingHom.isIntegralElem_zero

-- The former 02JJ-tagged declaration for the equivalence `finite ↔ integral + finite type`
-- is now the Mathlib theorem; the remaining 02JJ declaration below supplies the
-- equivalence with being generated by finitely many integral elements.
add_to_stacks 02JJ "finite = integral + finite type"
  Algebra.finite_iff_isIntegral_and_finiteType
add_to_ega "0 1.0.5" Algebra.finite_iff_isIntegral_and_finiteType
add_to_ega "II 6.1.2" "more general" Algebra.finite_iff_isIntegral_and_finiteType

/-- An algebra is module-finite if and only if it is generated as an algebra by a
finite set of integral elements. -/
@[stacks 02JJ, ega "II 6.1.2" "more general"]
theorem Algebra.finite_iff_exists_finset_adjoin_eq_top_and_isIntegral
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    Module.Finite R S ↔
      ∃ (s : Finset S), Algebra.adjoin R (s : Set S) = ⊤ ∧ ∀ x ∈ s, IsIntegral R x := by
  refine ⟨fun _ => ?_, fun ⟨s, hs, hint⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R S).out
    exact ⟨s, hs, fun x _ => Algebra.IsIntegral.isIntegral x⟩
  · have := fg_adjoin_of_finite s.finite_toSet fun x hx ↦ hint x (Finset.mem_coe.mp hx)
    rw [hs, Algebra.top_toSubmodule] at this
    exact ⟨this⟩

-- The former @[stacks 02JK] declarations are now the Mathlib theorems.
add_to_stacks 02JK "(1)" Algebra.IsIntegral.tensorProduct
add_to_ega "II 6.1.5" "(iii), integral, affine"
  Algebra.IsIntegral.tensorProduct
add_to_stacks 02JK "(2)" Module.Finite.base_change
add_to_sga "1 III 1.4" "partial" Module.Finite.base_change
add_to_ega "III 2.6.2.1" "special case" Module.Finite.base_change
add_to_ega "II 6.1.5" "(iii), finite, affine" Module.Finite.base_change

-- The former @[stacks 02JM] declarations are now the Mathlib theorems.
add_to_stacks 02JM "(1)" RingHom.IsIntegral.tower_top
add_to_ega "II 6.1.5" "(v), special case" RingHom.IsIntegral.tower_top
add_to_stacks 02JM "(2)" RingHom.Finite.of_comp_finite

-- The former @[stacks 00GN] declaration is now the Mathlib theorem.
add_to_stacks 00GN "integrality is stable under composition" RingHom.IsIntegral.trans
add_to_ega "II 6.1.5" "(ii), integral, affine" RingHom.IsIntegral.trans

-- The former @[stacks 00GK] declaration is now Mathlib's `RingHom.Finite.to_isIntegral`,
-- which already carries the tag upstream.

/-!
# Integrality over `R` after scaling by the leading coefficient

Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S` be integral over `R[x]`.
Suppose `φ p * t` lies in the image of `φ` for some `p ∈ R[x]` which is **not** assumed monic.
Then `t` becomes integral over `R` after being scaled by a power of the image of the leading
coefficient `a` of `p` and having the image of a single polynomial subtracted: there are
`q ∈ R[x]` and `n ≥ 0` with `φ a ^ n * t - φ q` integral over `R`.

This is Lemma 00PT with the monicity of `p` dropped, and it is the source's Lemma 00PT applied
after inverting `a`: over `R' = R[1/a]` the polynomial `p / a` is monic, so 00PT produces a
`q' ∈ R'[x]` with `t - φ' q'` integral over `R'`; clearing denominators writes `a ^ n q'` as the
image of some `q ∈ R[x]`, so `φ a ^ n t - φ q` is an element of `S` whose image in `S[1/a]` is
integral over `R'`, and Lemma 0307 converts that back into integrality over `R` at the cost of one
further factor `φ a ^ m`.

The scaling factor cannot be dispensed with, which is exactly why this lemma and 00PT are two
statements rather than one: see the witness in the implementation notes below.

## Main results

* `RingHom.exists_isIntegralElem_leadingCoeff_pow_mul_sub_of_isIntegralElem_of_mul_mem_range`:
  Stacks 00PV.

## Implementation notes

*`φ` is a bare ring map, as in the source, and not an `R`-algebra map.* Mathlib's
`exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range` carries the tag
00PV already, stated for `φ : R[X] →ₐ[R] S` with conclusion `IsIntegral R (a ^ n • t - φ q)`; that
form presupposes an `Algebra R S` structure and asserts integrality over `R` with respect to *it*.
Here, as in the companion statement of Tag 00PT, integrality over `R` is integrality along `φ.comp Polynomial.C`,
so no algebra structure on `S` is assumed and none has to be compatible with `φ`. The two
statements are inter-derivable — the algebra form is this one along
`(φ : R[X] →+* S).comp C = algebraMap R S`, and this one is the algebra form for the structure
`(φ.comp C).toAlgebra` — so nothing is lost, and the version stated here is the one that applies to
a ring map `R[x] → S` whose target already carries an unrelated `R`-algebra structure. For the same
reason the scalar action `a ^ n • t` of the algebra form is spelled `(φ.comp C) a ^ n * t`, which
is literally the source's `φ(a_k)^n t`.

*The source's `a_k` is `p.leadingCoeff`.* The source writes `p = a₀ + a₁x + … + a_k x^k` and scales
by `a_k`, i.e. by `p.coeff k` for a `k` with `p.natDegree ≤ k`. Only `k = p.natDegree` carries
content: for `k > p.natDegree` one has `a_k = 0` and the conclusion holds vacuously with `n = 1`
and `q = 0`, so no generality is lost by fixing `a = p.leadingCoeff`, and that is also the spelling
Mathlib's tagged form and its consumer 00PX use. Degenerate `p` need no separate hypothesis: for
`p = 0` the conclusion is again vacuous, and for monic `p` it is Lemma 00PT with `n = 0`.

*Faithfulness.* (1) Both hypotheses are used: without `ht` the statement is false (`R = ℤ`,
`S = ℚ`, `φ : ℤ[x] → ℚ` sending `x ↦ 0`, `t = 1/2`, `p = x + 2`, where `φ p * t = 1 ∈ φ.range` and
`a = 1`, but `1/2 - m ∉ ℤ` for every `m ∈ ℤ`), and without `hp` it is false as well (`R = ℤ`,
`S = ℚ(√2)`, `φ : x ↦ 1/2`, `t = √2/2`, `p = 3`, where `t² = φ x` gives `ht` while `3^n √2/2` has
half-integral `√2`-coefficient, so it stays outside `ℤ[√2]` after subtracting any element of
`φ.range ⊆ ℚ`). (2) The bases are the source's: integrality over `R[x]` is along `φ` itself and
integrality over `R` is along `φ.comp C`, not over `S` and not over the auxiliary ring `R[1/a]`
used in the proof. (3) The source names no canonical `q` or `n` and its consumer 00PX uses only
their existence, so the conclusion is existential; what the statement does pin is the structure map
`R → S`, which is `φ` on constants rather than an independent instance. (4) A non-degenerate
instance, in which the scaling is genuinely required: `R = ℤ`, `S = ℚ(√2)`, `φ : ℤ[x] → S` sending
`x ↦ 1/2`, `t = √2/2` and `p = 2x - 1`, so `a = 2` and `p` is not monic. Then `t² = 1/2 = φ x`
gives `ht`, `φ p = 0` gives `hp`, and `n = 1`, `q = 0` works since `2 * (√2/2) = √2` is integral
over `ℤ`; but `n = 0` is impossible, because `√2/2 - φ q` has `√2`-coefficient `1/2` for every
`q ∈ ℤ[x]` and the elements of `ℚ(√2)` integral over `ℤ` are `ℤ[√2]`. In particular `t` is not
itself integral over `R`, and Lemma 00PT does not apply to this `p`.

## References

* [StacksProject 00PV](https://stacks.math.columbia.edu/tag/00PV), Lemma 10.123.3
  (`algebra-lemma-combine-lemmas`), in Section 10.123 "Zariski's Main Theorem".
* [StacksProject 00PT](https://stacks.math.columbia.edu/tag/00PT), the monic case, from which the
  source deduces this lemma.
* [StacksProject 0307](https://stacks.math.columbia.edu/tag/0307), integrality after inverting one
  element, the second input to the source's proof.
-/

@[expose] public section

open Polynomial

/-- **Stacks 00PV.** Let `R` be a ring, let `φ : R[x] → S` be a ring map and let `t ∈ S`. If `t`
is integral over `R[x]` and `φ p * t` lies in the image of `φ` for some `p ∈ R[x]`, then there are
`q ∈ R[x]` and `n ≥ 0` such that `φ a ^ n * t - φ q` is integral over `R`, where `a` is the leading
coefficient of `p` and integrality over `R` is integrality along `φ.comp Polynomial.C`.

This is Lemma 00PT without the assumption that `p` is monic; the scaling by `φ a ^ n` is the price
of dropping it, and cannot be removed. -/
public theorem
    RingHom.exists_isIntegralElem_leadingCoeff_pow_mul_sub_of_isIntegralElem_of_mul_mem_range
    {R S : Type*} [CommRing R] [CommRing S] (φ : R[X] →+* S) (t : S) (p : R[X])
    (ht : φ.IsIntegralElem t) (hp : φ p * t ∈ φ.range) :
    ∃ (q : R[X]) (n : ℕ), (φ.comp (Polynomial.C : R →+* R[X])).IsIntegralElem
      ((φ.comp (Polynomial.C : R →+* R[X])) p.leadingCoeff ^ n * t - φ q) := by
  -- For the tower along `φ` and `φ ∘ C`, the canonical algebra homomorphism is `φ`.
  let _ : Algebra R[X] S := φ.toAlgebra
  let _ : Algebra R S := (φ.comp C).toAlgebra
  have : IsScalarTower R R[X] S :=
    .of_algebraMap_eq' (congrArg φ.comp Polynomial.algebraMap_eq.symm)
  obtain ⟨q, n, hq⟩ :=
    exists_isIntegral_leadingCoeff_pow_smul_sub_of_isIntegralElem_of_mul_mem_range
      (IsScalarTower.toAlgHom R R[X] S) t p
      (by rwa [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom])
      (by
        rw [AlgHom.mem_range]
        simp only [IsScalarTower.toAlgHom_apply]
        exact RingHom.mem_range.mp hp)
  rw [Algebra.smul_def, map_pow, IsScalarTower.toAlgHom_apply] at hq
  exact ⟨q, n, hq⟩

end
