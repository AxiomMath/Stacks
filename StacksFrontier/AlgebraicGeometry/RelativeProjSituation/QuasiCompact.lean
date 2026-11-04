module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Quasi-compactness of a relative `Proj`, and of a blowup in a finite-type ideal

The structure morphism of a relative `Proj` is quasi-compact as soon as each of its charts is a
quasi-compact scheme: the part of the relative `Proj` lying over an affine open `W` of the base
*is* the chart over `W`, by `Stacks.RelativeProj.Situation.relativeProjChart_isPullback`, and
quasi-compactness of a morphism is tested on affine opens of the target.

For the blowup of a scheme `X` in a quasi-coherent ideal sheaf `I` the charts are the projective
spectra of the graded rings of local sections of the Rees algebra, and this file shows each of
them is quasi-compact when `I` is of finite type. Over an affine open `V` the degree `n` sections
of the Rees algebra are the elements of the `n`-th power `I(V)ⁿ`, so finitely many generators of
`I(V)` give finitely many degree-one elements of the section ring whose standard opens cover the
chart; `AlgebraicGeometry.Proj.compactSpace_iff` then applies.

## Main definitions

* `Stacks.Blowup.reesSectionAmbient`: the ambient function of a degree `n` section of the Rees
  algebra over an affine open, an element of the `n`-th power of the ideal there.
* `Stacks.Blowup.reesSectionLift`: a degree `n` section of the Rees algebra with a prescribed
  ambient function.
* `Stacks.Blowup.reesLiftIdeal`: the ideal of ambient functions whose degree `n` lift lies in a
  given ideal of the graded section ring.

## Main results

* `Stacks.RelativeProj.Situation.quasiCompact_relativeProjToBase`: the structure morphism of a
  relative `Proj` whose charts are quasi-compact is quasi-compact.
* `Stacks.Blowup.compactSpace_proj_reesSectionRingGrading`: the blowup chart over an affine open
  on which the ideal is finitely generated is quasi-compact.
* `Stacks.Blowup.quasiCompact_blowUpToBase`: the blowup of a scheme in a finite-type
  quasi-coherent ideal sheaf is quasi-compact over the scheme.

## Implementation notes

`AlgebraicGeometry.reesSituation` carries its affine-local description through
`AlgebraicGeometry.reesAlgebraData`, which is a `Classical.choice` of
`AlgebraicGeometry.exists_reesAlgebraData` and is therefore *not* reducible to the concrete
`AlgebraicGeometry.reesGradedAlgebra`. So the degree `n` sections over an affine open are reached
only through the fields of `AlgebraicGeometry.ReesAlgebraData` — `pieceEquiv` and its
multiplicativity — and not through the ambient-function lemmas of
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/Basic.lean`, which are stated for the concrete
construction and are in any case `private` there.

Two bookkeeping points govern the shape of the proofs.

`AlgebraicGeometry.ReesAlgebraData.pieceEquiv` is indexed by `n : ℤ` with its target
`I(V) ^ n.toNat`, while `Stacks.RelativeProj.Situation.sectionPieces` is indexed by `n : ℕ`.
Rewriting
`((n : ℤ)).toNat = n` inside a membership statement is not type-correct, because the subtype the
element lives in mentions the exponent; the cure used here is to transport along the *ideal*
equality `I(V) ^ ((n : ℤ)).toNat = I(V) ^ n` with `Eq.le`, where the motive is plain membership.

`Stacks.RelativeProj.Situation.SectionRingStructure.mul_homogeneous` is an `HEq`, because the
product of a degree `n` and a degree `m` section lands in `sectionPieces ((n + m : ℕ) : ℤ)` while
the graded algebra's multiplication lands in `sectionPieces ((n : ℤ) + (m : ℤ))`. The two degrees
are equal but not definitionally so, so the multiplicativity of the ambient function is proved by
generalizing the degree to a variable `k : ℤ`, substituting `k = (n : ℤ) + (m : ℤ)`, and only then
using `eq_of_heq`.

Multiplication by a scalar is written `x * c` rather than `c * x`, and the inductive step uses
`I(V) ^ (n + 1) = I(V) ^ n * I(V)`, so that every degree appearing is of the form `n + m` with the
second summand a literal: `n + 0` and `n + 1` reduce to `n` and `n.succ` definitionally, whereas
`0 + n` does not.

## References

* [Stacks Project, Tag 01MD](https://stacks.math.columbia.edu/tag/01MD)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

/-- **The structure morphism of a relative `Proj` with quasi-compact charts is quasi-compact.**
Quasi-compactness of a morphism is tested on the affine opens of the target, and the part of the
relative `Proj` lying over an affine open of the base is exactly the chart there. -/
public theorem quasiCompact_relativeProjToBase (s : Situation.{u})
    (hc : ∀ W : s.base.affineOpens, CompactSpace (Proj (s.sectionRingGrading W.1))) :
    QuasiCompact (relativeProjToBase s) := by
  rw [AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen]
  intro V hV
  have hpre : relativeProjToBase s ⁻¹ᵁ V = ((chartData s).chartι ⟨V, hV⟩).opensRange :=
    (chartData s).toBase_preimage_coe ⟨V, hV⟩
  rw [hpre]
  have := hc ⟨V, hV⟩
  exact isCompact_range (Scheme.Hom.continuous _)

end Stacks.RelativeProj.Situation

namespace Stacks.Blowup

open Stacks.RelativeProj

variable {X : Scheme.{u}} (I : X.IdealSheafData) (V : X.affineOpens)

/-! ### The ambient function of a section of the Rees algebra

Over an affine open `V`, `AlgebraicGeometry.ReesAlgebraData.pieceEquiv` identifies the degree `n`
sections of the Rees algebra of `I` with the `n`-th power of `I(V)`. Composing with the inclusion
of that power into `Γ(X, V)` gives an injective additive, multiplicative map, which is all the
span argument below needs. -/

/-- The ambient function of a degree `n` section of the Rees algebra of `I` over the affine open
`V`: its image in `Γ(X, V)` under the identification of the degree `n` sections with `I(V)ⁿ`. -/
public def reesSectionAmbient (n : ℕ)
    (a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n) : Γ(X, V.1) :=
  (((AlgebraicGeometry.reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V a :
    ↥(I.ideal V ^ ((n : ℤ)).toNat)) : Γ(X, V.1))

@[simp]
public theorem reesSectionAmbient_zero (n : ℕ) : reesSectionAmbient I V n 0 = 0 := by
  simp [reesSectionAmbient]

public theorem reesSectionAmbient_add (n : ℕ)
    (a b : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n) :
    reesSectionAmbient I V n (a + b) =
      reesSectionAmbient I V n a + reesSectionAmbient I V n b := by
  simp [reesSectionAmbient]

/-- The ambient function of a degree `n` section lies in the `n`-th power of the ideal. -/
public theorem reesSectionAmbient_mem (n : ℕ)
    (a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n) :
    reesSectionAmbient I V n a ∈ I.ideal V ^ n :=
  (show I.ideal V ^ ((n : ℤ)).toNat = I.ideal V ^ n by rw [Int.toNat_natCast]).le
    ((AlgebraicGeometry.reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V a).2

/-- A section of the Rees algebra over an affine open is determined by its ambient function. -/
public theorem reesSectionAmbient_injective (n : ℕ) :
    Function.Injective (reesSectionAmbient I V n) := fun _ _ hab =>
  ((AlgebraicGeometry.reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V).injective
    (Subtype.ext hab)

/-- Every element of the `n`-th power of the ideal is the ambient function of a degree `n`
section. -/
public theorem exists_reesSectionAmbient_eq (n : ℕ) (x : Γ(X, V.1)) (hx : x ∈ I.ideal V ^ n) :
    ∃ a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n,
      reesSectionAmbient I V n a = x := by
  refine ⟨((AlgebraicGeometry.reesAlgebraData I).pieceEquiv (n : ℤ) (Int.natCast_nonneg n) V).symm
    ⟨x, by rwa [Int.toNat_natCast]⟩, ?_⟩
  simp [reesSectionAmbient]

/-- The ambient function is multiplicative for the graded multiplication of the section ring. -/
public theorem reesSectionAmbient_mul (n m : ℕ)
    (a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n)
    (b : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 m) :
    reesSectionAmbient I V (n + m) (GradedMonoid.GMul.mul a b) =
      reesSectionAmbient I V n a * reesSectionAmbient I V m b := by
  have key : ∀ (k : ℤ) (hk : 0 ≤ k), k = (n : ℤ) + (m : ℤ) →
      ∀ (c : ((AlgebraicGeometry.reesAlgebraData I).algebra.piece k).val.obj (op V.1)),
      HEq c (((AlgebraicGeometry.reesAlgebraData I).algebra.mul (n : ℤ) (m : ℤ)).app (op V.1) a b) →
      (((AlgebraicGeometry.reesAlgebraData I).pieceEquiv k hk V c :
          ↥(I.ideal V ^ k.toNat)) : Γ(X, V.1)) =
        reesSectionAmbient I V n a * reesSectionAmbient I V m b := by
    intro k hk hk2 c hc
    subst hk2
    rw [eq_of_heq hc]
    exact (AlgebraicGeometry.reesAlgebraData I).pieceEquiv_mul (n : ℤ) (m : ℤ)
      (Int.natCast_nonneg n) (Int.natCast_nonneg m) V a b
  exact key ((n + m : ℕ) : ℤ) (Int.natCast_nonneg _) (by push_cast; ring) _
    ((Situation.sectionRingStructure (AlgebraicGeometry.reesSituation I)).mul_homogeneous
      V.1 n m a b)

/-! ### The chosen lift of an ambient function -/

/-- A degree `n` section of the Rees algebra of `I` over `V` whose ambient function is the given
element of `I(V)ⁿ`. -/
public def reesSectionLift (n : ℕ) (y : ↥(I.ideal V ^ n)) :
    (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n :=
  (exists_reesSectionAmbient_eq I V n y.1 y.2).choose

@[simp]
public theorem reesSectionAmbient_reesSectionLift (n : ℕ) (y : ↥(I.ideal V ^ n)) :
    reesSectionAmbient I V n (reesSectionLift I V n y) = y.1 :=
  (exists_reesSectionAmbient_eq I V n y.1 y.2).choose_spec

public theorem reesSectionLift_reesSectionAmbient (n : ℕ)
    (a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n)
    (h : reesSectionAmbient I V n a ∈ I.ideal V ^ n) :
    reesSectionLift I V n ⟨reesSectionAmbient I V n a, h⟩ = a :=
  reesSectionAmbient_injective I V n (reesSectionAmbient_reesSectionLift I V n _)

public theorem reesSectionLift_zero (n : ℕ) (h : (0 : Γ(X, V.1)) ∈ I.ideal V ^ n) :
    reesSectionLift I V n ⟨0, h⟩ = 0 :=
  reesSectionAmbient_injective I V n (by
    rw [reesSectionAmbient_reesSectionLift, reesSectionAmbient_zero])

public theorem reesSectionLift_add (n : ℕ) (x y : Γ(X, V.1)) (hx : x ∈ I.ideal V ^ n)
    (hy : y ∈ I.ideal V ^ n) (hxy : x + y ∈ I.ideal V ^ n) :
    reesSectionLift I V n ⟨x + y, hxy⟩ =
      reesSectionLift I V n ⟨x, hx⟩ + reesSectionLift I V n ⟨y, hy⟩ :=
  reesSectionAmbient_injective I V n (by
    rw [reesSectionAmbient_reesSectionLift, reesSectionAmbient_add,
      reesSectionAmbient_reesSectionLift, reesSectionAmbient_reesSectionLift])

public theorem reesSectionLift_mul (n m : ℕ) (x y : Γ(X, V.1)) (hx : x ∈ I.ideal V ^ n)
    (hy : y ∈ I.ideal V ^ m) (hxy : x * y ∈ I.ideal V ^ (n + m)) :
    reesSectionLift I V (n + m) ⟨x * y, hxy⟩ =
      GradedMonoid.GMul.mul (reesSectionLift I V n ⟨x, hx⟩) (reesSectionLift I V m ⟨y, hy⟩) :=
  reesSectionAmbient_injective I V (n + m) (by
    rw [reesSectionAmbient_reesSectionLift, reesSectionAmbient_mul,
      reesSectionAmbient_reesSectionLift, reesSectionAmbient_reesSectionLift])

/-! ### The span argument -/

variable (T : Ideal ((AlgebraicGeometry.reesSituation I).sectionRing V.1))

public theorem mem_ideal_pow_zero (r : Γ(X, V.1)) : r ∈ I.ideal V ^ 0 := by simp

/-- The inclusion of a graded piece into the section ring turns the graded product into the ring
product. -/
private theorem of_gmul_eq_mul (n m : ℕ)
    (a : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 n)
    (b : (AlgebraicGeometry.reesSituation I).sectionPieces V.1 m) :
    DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) (n + m)
        (GradedMonoid.GMul.mul a b) =
      DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) n a *
        DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) m b :=
  (DirectSum.of_mul_of (A := (AlgebraicGeometry.reesSituation I).sectionPieces V.1) a b).symm

/-- The ambient functions of degree `n` whose chosen lift lies in the ideal `T` of the graded
section ring. It is an ideal of `Γ(X, V)` because the lift is additive and turns multiplication by
a function into multiplication by a degree-zero section. -/
public def reesLiftIdeal (n : ℕ) : Ideal Γ(X, V.1) where
  carrier := {x | ∃ h : x ∈ I.ideal V ^ n,
    DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) n
      (reesSectionLift I V n ⟨x, h⟩) ∈ T}
  zero_mem' := ⟨zero_mem _, by rw [reesSectionLift_zero, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro x y ⟨hx, hxT⟩ ⟨hy, hyT⟩
    refine ⟨add_mem hx hy, ?_⟩
    rw [reesSectionLift_add I V n x y hx hy, map_add]
    exact add_mem hxT hyT
  smul_mem' := by
    rintro c x ⟨hx, hxT⟩
    refine ⟨Submodule.smul_mem _ c hx, ?_⟩
    have hmulamb : reesSectionAmbient I V n
          (GradedMonoid.GMul.mul (reesSectionLift I V n ⟨x, hx⟩)
            (reesSectionLift I V 0 ⟨c, mem_ideal_pow_zero I V c⟩)) =
        reesSectionAmbient I V n (reesSectionLift I V n ⟨x, hx⟩) *
          reesSectionAmbient I V 0 (reesSectionLift I V 0 ⟨c, mem_ideal_pow_zero I V c⟩) :=
      reesSectionAmbient_mul I V n 0 _ _
    have heq : reesSectionLift I V n ⟨c • x, Submodule.smul_mem _ c hx⟩ =
        GradedMonoid.GMul.mul (reesSectionLift I V n ⟨x, hx⟩)
          (reesSectionLift I V 0 ⟨c, mem_ideal_pow_zero I V c⟩) := by
      refine reesSectionAmbient_injective I V n ?_
      rw [reesSectionAmbient_reesSectionLift, hmulamb, reesSectionAmbient_reesSectionLift,
        reesSectionAmbient_reesSectionLift]
      simp [smul_eq_mul, mul_comm]
    rw [heq]
    have hof : DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) n
        (GradedMonoid.GMul.mul (reesSectionLift I V n ⟨x, hx⟩)
          (reesSectionLift I V 0 ⟨c, mem_ideal_pow_zero I V c⟩)) =
        DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) n
            (reesSectionLift I V n ⟨x, hx⟩) *
          DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) 0
            (reesSectionLift I V 0 ⟨c, mem_ideal_pow_zero I V c⟩) :=
      (DirectSum.of_mul_of (A := (AlgebraicGeometry.reesSituation I).sectionPieces V.1)
        (i := n) (j := 0) _ _).symm
    rw [hof]
    exact Ideal.mul_mem_right _ _ hxT

/-- Once every element of the ideal has its degree-one lift in `T`, every element of every
positive power has its lift in `T`: a product of an element of `I(V)ⁿ` and an element of `I(V)`
lifts to the product of their lifts. -/
public theorem pow_succ_le_reesLiftIdeal (h1 : I.ideal V ≤ reesLiftIdeal I V T 1) (n : ℕ) :
    I.ideal V ^ (n + 1) ≤ reesLiftIdeal I V T (n + 1) := by
  rw [pow_succ]
  refine Submodule.mul_le.mpr ?_
  intro e he c hc
  obtain ⟨hc', hcT⟩ := h1 hc
  have hec : e * c ∈ I.ideal V ^ (n + 1) := by
    rw [pow_succ]; exact Submodule.mul_mem_mul he hc
  refine ⟨hec, ?_⟩
  rw [reesSectionLift_mul I V n 1 e c he hc' hec]
  rw [of_gmul_eq_mul I V n 1]
  exact Ideal.mul_mem_left _ _ hcT

variable {I V} in
/-- **The blowup chart over an affine open on which the ideal is finitely generated is
quasi-compact.** Finitely many generators of `I(V)` lift to finitely many degree-one elements of
the graded section ring; the irrelevant ideal is contained in the ideal they span, because the
degree `n` sections are `I(V)ⁿ` and `I(V)ⁿ = I(V)ⁿ⁻¹ · I(V)` for `n ≥ 1`. -/
public theorem compactSpace_proj_reesSectionRingGrading (hI : (I.ideal V).FG) :
    CompactSpace
      (AlgebraicGeometry.Proj ((AlgebraicGeometry.reesSituation I).sectionRingGrading V.1)) := by
  classical
  obtain ⟨G, hG⟩ := hI
  have hG1 : ∀ x ∈ G, x ∈ I.ideal V ^ 1 := by
    intro x hx; rw [pow_one, ← hG]; exact Ideal.subset_span hx
  set F : Finset ((AlgebraicGeometry.reesSituation I).sectionRing V.1) :=
    G.attach.image (fun x => DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces V.1) 1
      (reesSectionLift I V 1 ⟨x.1, hG1 x.1 x.2⟩)) with hF
  set T : Ideal ((AlgebraicGeometry.reesSituation I).sectionRing V.1) :=
    Ideal.span (F : Set _) with hT
  have h1 : I.ideal V ≤ reesLiftIdeal I V T 1 := by
    rw [← hG]
    refine Ideal.span_le.mpr ?_
    intro x hx
    exact ⟨hG1 x hx, Ideal.subset_span (by
      rw [hF]
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩))⟩
  have hhom : ∀ (n : ℕ), 0 < n →
      ∀ z ∈ (AlgebraicGeometry.reesSituation I).sectionRingGrading V.1 n, z ∈ T := by
    intro n hn z hz
    rw [Situation.sectionRingGrading, AddMonoidHom.mem_range] at hz
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨_hmem, hT'⟩ :=
      pow_succ_le_reesLiftIdeal I V T h1 m (reesSectionAmbient_mem I V (m + 1) a)
    rwa [reesSectionLift_reesSectionAmbient] at hT'
  rw [AlgebraicGeometry.Proj.compactSpace_iff]
  refine ⟨F, ?_, ?_⟩
  · intro f hf
    rw [hF] at hf
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨1, one_pos, AddMonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  · rw [HomogeneousIdeal.irrelevant_eq_span]
    refine Ideal.span_le.mpr ?_
    intro z hz
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hz
    obtain ⟨i, hi, hz⟩ := hz
    exact Ideal.le_radical (hhom i hi z hz)

variable {I} in
/-- **The blowup of a scheme in a finite-type quasi-coherent ideal sheaf is quasi-compact over the
scheme.** This is the quasi-compactness half of the relative ampleness of the blowup twist, Stacks
tag 02NS, and the half that does not mention the twist. -/
public theorem quasiCompact_blowUpToBase (hI : I.IsFiniteType) :
    QuasiCompact (blowUpToBase I) :=
  Situation.quasiCompact_relativeProjToBase (AlgebraicGeometry.reesSituation I) fun W =>
    compactSpace_proj_reesSectionRingGrading (hI W)

end Stacks.Blowup

end
