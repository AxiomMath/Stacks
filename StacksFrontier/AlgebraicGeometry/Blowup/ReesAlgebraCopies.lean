module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IdealSheafPowers
public import StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Modules.ClosedSubschemeQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# The two Rees algebras of an ideal sheaf are the same Rees algebra

The Rees algebra `⨁_{n ≥ 0} 𝓘ⁿ` of a sheaf of ideals is built twice in this library, and the two
constructions do not meet:

* `SheafOfModules.reesGradedAlgebra`, for a sheaf submodule `𝓘 ⊆ 𝒪` of the structure sheaf of a
  ringed site. Its degree-`n` piece `SheafOfModules.reesPiece` is a *coerced submodule* of the
  structure sheaf, so a local section of it is a section of `𝒪` together with a proof, read by
  `SheafOfModules.reesVal`; its multiplication `SheafOfModules.reesMul` is one uniform bilinear
  map, and its powers are `SheafOfModules.idealSheafPow`, defined by the covering sieve of opens
  over which a section lies in the `n`-th power of the ideal of sections.
* `Stacks.Blowup.reesGradedAlgebra`, for an `AlgebraicGeometry.Scheme.IdealSheafData` on a scheme.
  Its degree-`n` piece `Stacks.Blowup.reesPiece` is a *categorical kernel*, of
  `𝒪_X ⟶ (ι_{Iⁿ})_* 𝒪_{V(Iⁿ)}`, read into `𝒪_X` by `Stacks.Blowup.reesPieceAmbient`; its
  multiplication `Stacks.Blowup.reesMultiplication` is built by case analysis on the signs of the
  two integer degrees, and its powers are the monoid powers of `Scheme.IdealSheafData`, given by
  their ideal of sections over each *affine* open.

This file identifies them, as sheaves of graded algebras: `Stacks.Blowup.reesGradedAlgebraIso`.

## Main results

* `Stacks.Blowup.unitSubmodule_pow` — **the index types agree**: the ideal sheaf of the
  `Scheme.IdealSheafData` power `Iⁿ` is the sheaf-submodule power
  `SheafOfModules.idealSheafPow` of the ideal sheaf of `I`.
* `Stacks.Blowup.reesPieceIso` — **the pieces agree**, in every integer degree.
* `Stacks.Blowup.reesPieceIso_hom_reesMul` — **the multiplications agree** across that
  identification, in every pair of integer degrees.
* `Stacks.Blowup.reesGradedAlgebraIso` — the resulting isomorphism of sheaves of graded algebras.
* `Stacks.Blowup.reesMulSheaf` and `reesMulSheaf_assoc` — the multiplication of
  `Stacks.Blowup.reesGradedAlgebra` as a morphism out of the tensor product sheaf, and its
  associativity.

## How the index types are matched

Everything rests on `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, the ideal sheaf of
`I` read as a submodule of the structure sheaf — which is already the *sectionwise* kernel of the
very morphism whose categorical kernel is `Stacks.Blowup.reesPiece`. So the piece-level
comparison is `AlgebraicGeometry.SheafOfModules.Submodule.kernelIso` and costs nothing, and the
whole content of the identification is `unitSubmodule_pow`.

That equation might look like it needs quasi-coherence of `Iⁿ`: the right-hand side is a
sheafified power, so its sections over an affine open are *a priori* larger than the `n`-th power
of the ideal there, and showing they are not is the quasi-coherence statement. **It does not.**
Both sides are `SheafOfModules.Submodule`s, so membership in either is local, and the affine opens
form a basis (`AlgebraicGeometry.Scheme.isBasis_affineOpens`, through
`Stacks.Algebraization.mem_submodule_of_affine`). Each containment is therefore checked after
restriction to an affine open:

* `≤` is `SheafOfModules.mem_idealSheafPow_of_mem_pow` applied on an affine open, where the
  sections of the left-hand side are `(I.ideal U)ⁿ` by
  `Scheme.IdealSheafData.unitSubmodule_obj_affine` and `Scheme.IdealSheafData.ideal_pow`;
* `≥` never evaluates the sheafified power at all. A section of it comes with its own covering
  sieve, `SheafOfModules.powSieve`, over each arm of which the section is an honest product of
  `n` sections of `𝓘`; `pow_idealAt_unitSubmodule_le` puts such a product into the ideal sheaf of
  `Iⁿ`, and locality of that sheaf submodule finishes.

The exact-value statement — that the sections of `SheafOfModules.idealSheafPow` over an affine
open are the `n`-th power of the ideal there — is a *consequence* of `unitSubmodule_pow` and
`Scheme.IdealSheafData.unitSubmodule_obj_affine`, not an input to it.

## The multiplication is cheap, and so is its morphism-level reading

Both multiplications compute, on local sections, to the product of the two sections of `𝒪_X`:
copy A by `SheafOfModules.reesVal_reesMul_app`, copy B by
`Stacks.Blowup.reesMultiplication_ambient`. The identification of the pieces carries `reesVal` to
`reesPieceAmbient` (`reesPieceAmbient_reesPieceIso_hom`, which is
`AlgebraicGeometry.SheafOfModules.Submodule.kernelIso_hom_comp_ι` on sections), and in a
nonnegative degree a section is determined by its ambient section
(`Stacks.Blowup.reesPieceAmbient_injective`). In a negative degree both multiplications vanish,
copy A because the first or second factor is a section of the zero sheaf of ideals and copy B
because its sign split puts the zero bilinear map there. So the sign split is no obstruction: it
is dispatched by two lemmas, and no case of it is ever compared with a case of the uniform map.

**The morphism-level multiplication of `Stacks.Blowup.reesGradedAlgebra` needs none of the above.**
`SheafOfModules.GradedAlgebra.mulSheaf` and `Stacks.TensorSheafWorld.mulSheaf_assoc` are
statements about an *arbitrary* sheaf of graded algebras over a ring sheaf of the form
`CategoryTheory.Sheaf.toRingCat J O♯`; `X.ringCatSheaf` is of that form — it is definitionally
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`, which is `toRingCat` applied to
`X.sheaf` — so they apply to the Rees algebra of an ideal sheaf on a scheme directly.
`reesMulSheaf` and `reesMulSheaf_assoc` record that. Neither copy of the Rees algebra is
privileged in this respect: `SheafOfModules.reesGradedAlgebra` is stated over a bare
`Sheaf J RingCat` and has to be re-seated on a `toRingCat` ring sheaf — which is what
`SheafOfModules.reesGradedAlgebraOfRingedSite` does — before `mulSheaf` reaches it either.

## Implementation notes

The commutativity assumption that `SheafOfModules.reesGradedAlgebra` takes is
`Stacks.AlgebraicGeometry.AnnihilatorQcoh.mul_comm_ringCatSheaf`, which is why
`StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic` — otherwise unrelated to this file — is
imported. It is a four-line lemma and re-proving it here would cost no import at all, but there
would then be two public declarations of one statement at one spelling, under two namespaces,
which is the defect this file exists to repair one instance of; `newdups` does not report that
pair, because the two statements are not written identically.

## No new tag site

Tag 0FQW is carried by `SheafOfModules.reesGradedAlgebra` and Tag 01OG by
`Stacks.Blowup.exists_reesAlgebraData`; these declarations say that those two name one object,
which is a spelling and not a second proof of either.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.AnnihilatorQcoh (mul_comm_ringCatSheaf)

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Over an affine open, the sections of the ideal sheaf of `I` are `I`'s own ideal there, in the
`SheafOfModules.idealAt` spelling that the powers of a sheaf of ideals are stated in. -/
public theorem idealAt_unitSubmodule_affine (V : X.affineOpens) :
    SheafOfModules.idealAt I.unitSubmodule (op V.1) = I.ideal V :=
  I.unitSubmodule_obj_affine V

/-- **Over an affine open, the sections of the ideal sheaf of `Iⁿ` are the `n`-th power of the
sections of the ideal sheaf of `I`.** -/
public theorem idealAt_unitSubmodule_pow_affine (n : ℕ) (V : X.affineOpens) :
    SheafOfModules.idealAt (I ^ n).unitSubmodule (op V.1) =
      SheafOfModules.idealAt I.unitSubmodule (op V.1) ^ n := by
  rw [idealAt_unitSubmodule_affine (I ^ n) V, idealAt_unitSubmodule_affine I V]
  exact congrFun (Scheme.IdealSheafData.ideal_pow I n) V

/-- **A product of `n` local sections of the ideal sheaf of `I`, over an arbitrary open, is a
section of the ideal sheaf of `Iⁿ`.** The containment is checked on the affine opens, where both
sides are computed, and carried to an arbitrary open because the target is a sheaf submodule. -/
public theorem pow_idealAt_unitSubmodule_le (n : ℕ) (U : (Opens X)ᵒᵖ) :
    SheafOfModules.idealAt I.unitSubmodule U ^ n ≤
      SheafOfModules.idealAt (I ^ n).unitSubmodule U := by
  intro a ha
  refine Stacks.Algebraization.mem_submodule_of_affine (I ^ n).unitSubmodule U.unop a
    fun V i ↦ ?_
  change _ ∈ SheafOfModules.idealAt (I ^ n).unitSubmodule (op V.1)
  rw [idealAt_unitSubmodule_pow_affine I n V]
  exact SheafOfModules.map_mem_idealAt_pow i.op n ha

/-- **The ideal sheaf of `Iⁿ` is the `n`-th power of the ideal sheaf of `I`.** On the left is the
`AlgebraicGeometry.Scheme.IdealSheafData` power, given by its ideal of sections over each affine
open; on the right is `SheafOfModules.idealSheafPow`, given by the covering sieve of opens over
which a section lies in the `n`-th power of the ideal of sections. -/
public theorem unitSubmodule_pow (n : ℕ) :
    (I ^ n).unitSubmodule = SheafOfModules.idealSheafPow I.unitSubmodule n := by
  refine le_antisymm (SheafOfModules.idealSheaf_le fun U a ha ↦ ?_)
    (SheafOfModules.idealSheaf_le fun U a ha ↦ ?_)
  · refine Stacks.Algebraization.mem_submodule_of_affine
      (SheafOfModules.idealSheafPow I.unitSubmodule n) U.unop a fun V i ↦ ?_
    change _ ∈ SheafOfModules.idealAt (SheafOfModules.idealSheafPow I.unitSubmodule n) (op V.1)
    refine SheafOfModules.mem_idealSheafPow_of_mem_pow I.unitSubmodule n ?_
    rw [← idealAt_unitSubmodule_pow_affine I n V]
    exact SheafOfModules.map_mem_idealAt (I := (I ^ n).unitSubmodule) i.op ha
  · exact SheafOfModules.mem_idealAt_of_sieve (I ^ n).unitSubmodule a
      (SheafOfModules.powSieve I.unitSubmodule n a) ha
      fun {W} f hf ↦ pow_idealAt_unitSubmodule_le I n (op W) hf

/-- The degree-`k` piece of the integer-indexed family of powers is the ideal sheaf of `Iᵏ`. -/
public theorem idealSheafZPow_unitSubmodule_natCast (k : ℕ) :
    SheafOfModules.idealSheafZPow I.unitSubmodule (k : ℤ) = (I ^ k).unitSubmodule :=
  (SheafOfModules.idealSheafZPow_natCast I.unitSubmodule k).trans (unitSubmodule_pow I k).symm

/-- **The degree-`k` pieces of the two Rees algebras agree, for `k ≥ 0`.** On the left the piece
is a coerced submodule of the structure sheaf, on the right a categorical kernel; the two are
identified by `AlgebraicGeometry.SheafOfModules.Submodule.kernelIso`. -/
public def reesPieceIsoOfNat (k : ℕ) :
    SheafOfModules.reesPiece I.unitSubmodule (k : ℤ) ≅ reesPiece I (k : ℤ) :=
  eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
      (idealSheafZPow_unitSubmodule_natCast I k)) ≪≫
    Stacks.ClosedSubscheme.unitSubmoduleIsoKernel (I ^ k)

/-- In a negative degree the underlying section of a local section of copy A's piece is zero. -/
private theorem reesVal_eq_zero_of_neg {n : ℤ} (hn : n < 0) {U : (Opens X)ᵒᵖ}
    (z : (SheafOfModules.reesPiece I.unitSubmodule n).val.obj U) :
    SheafOfModules.reesVal I.unitSubmodule z = 0 :=
  SheafOfModules.eq_zero_of_mem_idealSheafZPow_neg I.unitSubmodule hn
    (SheafOfModules.reesVal_mem I.unitSubmodule z)

/-- In a negative degree the piece of copy A vanishes: the integer-indexed family of powers is
the zero sheaf of ideals there. -/
public theorem isZero_reesPiece_unitSubmodule_neg {n : ℤ} (hn : n < 0) :
    IsZero (SheafOfModules.reesPiece I.unitSubmodule n) := by
  rw [IsZero.iff_id_eq_zero]
  ext U z
  exact SheafOfModules.reesPiece_ext I.unitSubmodule (reesVal_eq_zero_of_neg I hn z)

/-- **The pieces of the two Rees algebras agree in every integer degree.** In a nonnegative
degree this is `Stacks.Blowup.reesPieceIsoOfNat`; in a negative degree both pieces vanish. -/
public def reesPieceIso (n : ℤ) :
    SheafOfModules.reesPiece I.unitSubmodule n ≅ reesPiece I n :=
  match n with
  | .ofNat k => reesPieceIsoOfNat I k
  | .negSucc k =>
    (isZero_reesPiece_unitSubmodule_neg I (Int.negSucc_lt_zero k)).iso
      (reesPiece_negative_isZero I _ (Int.negSucc_lt_zero k))

/-- Transport of a coerced submodule of the structure sheaf along an equality of submodules does
not change the underlying section. Stated over two variable submodules, so that the equality can
be substituted. -/
public theorem val_eqToIso_hom_val_app
    {N M : (SheafOfModules.unit.{u} X.ringCatSheaf).Submodule} (h : N = M)
    (U : (Opens X)ᵒᵖ) (z : N.toSheafOfModules.val.obj U) :
    ((eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules h)).hom.val.app U z).1
      = z.1 := by
  subst h
  rfl

/-- **The identification of the degree-`k` pieces reads a local section the same way on both
sides**: copy A reads it with `SheafOfModules.reesVal`, copy B with
`Stacks.Blowup.reesPieceAmbient`, and the two agree across the identification. -/
public theorem reesPieceAmbient_reesPieceIso_hom (k : ℕ) (U : (Opens X)ᵒᵖ)
    (z : (SheafOfModules.reesPiece I.unitSubmodule (k : ℤ)).val.obj U) :
    reesPieceAmbient I (k : ℤ) U.unop ((reesPieceIso I (k : ℤ)).hom.val.app U z) =
      SheafOfModules.reesVal I.unitSubmodule z := by
  have hι := AlgebraicGeometry.SheafOfModules.Submodule.kernelIso_hom_comp_ι
    (Stacks.ClosedSubscheme.structureSheafProjection (I ^ k))
  have hstep := congrArg
    (fun φ : ((I ^ k).unitSubmodule.toSheafOfModules : X.Modules) ⟶
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) =>
      ConcreteCategory.hom (φ.val.app U)
        ((eqToIso (congrArg SheafOfModules.Submodule.toSheafOfModules
          (idealSheafZPow_unitSubmodule_natCast I k))).hom.val.app U z)) hι
  exact hstep.trans (val_eqToIso_hom_val_app (idealSheafZPow_unitSubmodule_natCast I k) U z)

/-- **The identification of the degree-`n` pieces reads a local section the same way on both
sides**, in every nonnegative degree. -/
public theorem reesPieceAmbient_reesPieceIso_hom_of_nonneg {n : ℤ} (hn : 0 ≤ n)
    (U : (Opens X)ᵒᵖ) (z : (SheafOfModules.reesPiece I.unitSubmodule n).val.obj U) :
    reesPieceAmbient I n U.unop ((reesPieceIso I n).hom.val.app U z) =
      SheafOfModules.reesVal I.unitSubmodule z := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact reesPieceAmbient_reesPieceIso_hom I k U z

/-! ### The two multiplications -/

/-- In a negative first degree copy A's multiplication vanishes: the first factor is a section of
the zero sheaf of ideals. -/
public theorem reesMul_app_eq_zero_of_neg_left {i : ℤ} (hi : i < 0) (j : ℤ) (U : (Opens X)ᵒᵖ)
    (x : (SheafOfModules.reesPiece I.unitSubmodule i).val.obj U)
    (y : (SheafOfModules.reesPiece I.unitSubmodule j).val.obj U) :
    (SheafOfModules.reesMul I.unitSubmodule (mul_comm_ringCatSheaf X) i j).app U x y = 0 :=
  SheafOfModules.reesPiece_ext I.unitSubmodule (by
    rw [SheafOfModules.reesVal_reesMul_app, reesVal_eq_zero_of_neg I hi x, zero_mul]
    rfl)

/-- In a negative second degree copy A's multiplication vanishes. -/
public theorem reesMul_app_eq_zero_of_neg_right (i : ℤ) {j : ℤ} (hj : j < 0) (U : (Opens X)ᵒᵖ)
    (x : (SheafOfModules.reesPiece I.unitSubmodule i).val.obj U)
    (y : (SheafOfModules.reesPiece I.unitSubmodule j).val.obj U) :
    (SheafOfModules.reesMul I.unitSubmodule (mul_comm_ringCatSheaf X) i j).app U x y = 0 :=
  SheafOfModules.reesPiece_ext I.unitSubmodule (by
    rw [SheafOfModules.reesVal_reesMul_app, reesVal_eq_zero_of_neg I hj y, mul_zero]
    rfl)

/-- In a negative first degree copy B's multiplication vanishes: it is the zero bilinear map
there, by the sign split in its construction. -/
public theorem reesMultiplication_app_eq_zero_of_neg_left {i : ℤ} (hi : i < 0) (j : ℤ)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) (b : (reesPiece I j).val.obj U) :
    (reesMultiplication I i j).app U a b = 0 := by
  cases i with
  | ofNat k => exact absurd hi (not_lt.mpr (Int.natCast_nonneg k))
  | negSucc k => rfl

/-- In a negative second degree copy B's multiplication vanishes. -/
public theorem reesMultiplication_app_eq_zero_of_neg_right (i : ℤ) {j : ℤ} (hj : j < 0)
    (U : (Opens X)ᵒᵖ) (a : (reesPiece I i).val.obj U) (b : (reesPiece I j).val.obj U) :
    (reesMultiplication I i j).app U a b = 0 := by
  cases i with
  | ofNat m =>
    cases j with
    | ofNat n => exact absurd hj (not_lt.mpr (Int.natCast_nonneg n))
    | negSucc n => rfl
  | negSucc m => rfl

/-- **The two multiplications agree across the identification of the pieces, in every pair of
integer degrees.** In nonnegative degrees both compute the product of the two ambient sections of
`𝒪_X` — copy A by `SheafOfModules.reesVal_reesMul_app`, copy B by
`Stacks.Blowup.reesMultiplication_ambient` — and a section of a nonnegative piece is determined by
its ambient section. If either degree is negative both sides vanish. -/
public theorem reesPieceIso_hom_reesMul (i j : ℤ) (U : (Opens X)ᵒᵖ)
    (x : (SheafOfModules.reesPiece I.unitSubmodule i).val.obj U)
    (y : (SheafOfModules.reesPiece I.unitSubmodule j).val.obj U) :
    (reesPieceIso I (i + j)).hom.val.app U
        ((SheafOfModules.reesMul I.unitSubmodule (mul_comm_ringCatSheaf X) i j).app U x y) =
      (reesMultiplication I i j).app U ((reesPieceIso I i).hom.val.app U x)
        ((reesPieceIso I j).hom.val.app U y) := by
  rcases lt_or_ge i 0 with hi | hi
  · rw [reesMul_app_eq_zero_of_neg_left I hi j U x y,
      reesMultiplication_app_eq_zero_of_neg_left I hi j U _ _]
    exact map_zero _
  rcases lt_or_ge j 0 with hj | hj
  · rw [reesMul_app_eq_zero_of_neg_right I i hj U x y,
      reesMultiplication_app_eq_zero_of_neg_right I i hj U _ _]
    exact map_zero _
  refine reesPieceAmbient_injective I (i + j) (by omega) U.unop ?_
  rw [reesPieceAmbient_reesPieceIso_hom_of_nonneg I (by omega : (0 : ℤ) ≤ i + j) U,
    reesMultiplication_ambient I i j U.unop,
    reesPieceAmbient_reesPieceIso_hom_of_nonneg I hi U,
    reesPieceAmbient_reesPieceIso_hom_of_nonneg I hj U,
    SheafOfModules.reesVal_reesMul_app]
  rfl

/-! ### The two Rees algebras -/

/-- Copy A's Rees graded algebra `⨁_{n ≥ 0} 𝓘ⁿ`, at the ideal sheaf of `I` read as a submodule of
the structure sheaf.

This is **not** a duplicate of `Stacks.Conormal.grGradedAlgebra`, and must not be replaced by an
alias of it. That is the *associated graded* algebra `⨁_{n ≥ 0} ℐⁿ/ℐⁿ⁺¹` of [Stacks, Tag 0633];
this is the *Rees* algebra `⨁_{n ≥ 0} 𝓘ⁿ`. The two share the type
`SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf`, which is why a statement-text duplicate scan
pairs them, but their bodies are unrelated — and identifying them would falsify
`Stacks.Blowup.reesGradedAlgebraIso` below, which asserts only that this algebra is isomorphic to
`Stacks.Blowup.reesGradedAlgebra`. -/
public def reesGradedAlgebraUnitSubmodule : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  SheafOfModules.reesGradedAlgebra I.unitSubmodule (mul_comm_ringCatSheaf X)

/-- **The two Rees algebras of an ideal sheaf are isomorphic as sheaves of graded algebras.**
On the left is `SheafOfModules.reesGradedAlgebra`, whose degree-`n` piece is a coerced submodule
of the structure sheaf and whose multiplication is one uniform bilinear map; on the right is
`Stacks.Blowup.reesGradedAlgebra`, whose degree-`n` piece is a categorical kernel and whose
multiplication is built by case analysis on the signs of the two degrees. -/
public def reesGradedAlgebraIso : reesGradedAlgebraUnitSubmodule I ≅ reesGradedAlgebra I :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso (reesPieceIso I) (reesPieceIso_hom_reesMul I)

/-! ### The multiplication of the Rees algebra as a morphism of sheaves of modules -/

/-- The Rees algebra of `I`, read at the `Stacks.RingedSpace.structureRingSheaf` spelling of the
structure sheaf of rings. It is the same object: `X.ringCatSheaf` and
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace` are definitionally equal, the latter being
`CategoryTheory.Sheaf.toRingCat` applied to `X.sheaf`. The spelling matters only to instance
search: `Stacks.PullbackGradedAlgebra.monoidalCategory`, which supplies the monoidal structure of
[Stacks, Tag 01CA], is keyed on it. -/
public def reesGradedAlgebraRingedSpace :
    SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) :=
  reesGradedAlgebra I

/-- **The multiplication of the Rees algebra of `I` in two integer degrees, as a morphism of
sheaves of modules out of the tensor product sheaf.**

`SheafOfModules.GradedAlgebra.mulSheaf` is a construction on an arbitrary sheaf of graded algebras
over a ring sheaf of the form `CategoryTheory.Sheaf.toRingCat J O♯`, and `X.ringCatSheaf` is of
that form, so it applies to `Stacks.Blowup.reesGradedAlgebra` directly.

The tensor product sheaf is named in the curried spelling
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the one
`SheafOfModules.GradedAlgebra.mulSheaf` states its own type in. The product-category reading of
the same bifunctor is `CategoryTheory.Functor.uncurry.obj` of it, and
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` is the comparison on morphisms. -/
public def reesMulSheaf (i j : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj (reesPiece I i)).obj
        (reesPiece I j) ⟶ reesPiece I (i + j) :=
  SheafOfModules.GradedAlgebra.mulSheaf (reesGradedAlgebra I) i j

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- **The multiplication of the Rees algebra of `I` is associative as an equation between
morphisms out of the twice-iterated tensor product sheaf.**

This is `Stacks.TensorSheafWorld.mulSheaf_assoc` at the Rees algebra. It needs no comparison with
`SheafOfModules.reesGradedAlgebra`: `mulSheaf` and its associativity are statements about an
arbitrary sheaf of graded algebras, and the Rees algebra of an ideal sheaf on a scheme is one.

The right whiskering is written as `CategoryTheory.MonoidalCategoryStruct.whiskerRight` with its
category argument named, exactly as `Stacks.TensorSheafWorld.mulSheaf_assoc` writes it, and for
the same reason: the domain of `SheafOfModules.GradedAlgebra.mulSheaf` is stated through
`Stacks.SheafOfModules.Tensor.sheafTensor`, so left-to-right elaboration of the `▷` notation
would read the ambient category off `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, at which
spelling the monoidal structure of [Stacks, Tag 01CA] is not registered. Naming the category at
the `Stacks.RingedSpace.structureRingSheaf` spelling is what
`Stacks.PullbackGradedAlgebra.monoidalCategory` is keyed on. The two spellings are definitionally
equal, so this is a choice of discrimination-tree key and not of monoidal structure. -/
public theorem reesMulSheaf_assoc (i j k : ℤ) :
    MonoidalCategoryStruct.whiskerRight
          (C := SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace))
          (SheafOfModules.GradedAlgebra.mulSheaf (reesGradedAlgebraRingedSpace I) i j)
          ((reesGradedAlgebraRingedSpace I).piece k) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (reesGradedAlgebraRingedSpace I) (i + j) k =
      (α_ ((reesGradedAlgebraRingedSpace I).piece i) ((reesGradedAlgebraRingedSpace I).piece j)
            ((reesGradedAlgebraRingedSpace I).piece k)).hom ≫
          (reesGradedAlgebraRingedSpace I).piece i ◁
            SheafOfModules.GradedAlgebra.mulSheaf (reesGradedAlgebraRingedSpace I) j k ≫
          SheafOfModules.GradedAlgebra.mulSheaf (reesGradedAlgebraRingedSpace I) i (j + k) ≫
            eqToHom (congrArg (reesGradedAlgebraRingedSpace I).piece (add_assoc i j k).symm) :=
  Stacks.TensorSheafWorld.mulSheaf_assoc X.sheaf
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isSheafStruct X)
    (reesGradedAlgebraRingedSpace I) i j k

end Stacks.Blowup

end
