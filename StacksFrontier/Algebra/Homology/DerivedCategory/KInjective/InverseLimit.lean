module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Limits of inverse systems of K-injective complexes

The limit of an inverse system of K-injective complexes with degreewise split surjective
transition maps is K-injective ([Stacks, Tag 070L]): `isKInjective_limit_of_inverseSystem`.
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project, Tag 070L (Lemma 13.31.8), in the chapter on Derived Categories
(Section 13.31, "K-injective complexes").

Let `A` be an abelian category, and let
`... → I₃ → I₂ → I₁`
be an inverse system of (cochain) complexes in `A` (indexed by the positive
integers, with transition maps going from larger to smaller index). Assume:

1. each complex `Iₙ` is K-injective (Tag 070H);
2. for every `n ≥ 1` and every degree `m`, the transition map `Iₙ₊₁^m → Iₙ^m`
   in degree `m` is a split surjection;
3. for every degree `m` the limit `I^m = lim_n Iₙ^m` exists in `A`, so that the
   limit complex `I` of the inverse system is defined.

Then the limit complex `I` is K-injective.
-/

/-
## Background and conventions

* `A` denotes an abelian category. We work with cochain complexes
  `CochainComplex A ℤ = HomologicalComplex A (ComplexShape.up ℤ)`; differentials
  raise degree by one and `dᵐ⁺¹ ∘ dᵐ = 0`.

* `K(A)`, the homotopy category, is `HomotopyCategory A (ComplexShape.up ℤ)`,
  obtained from chain complexes by passing to homotopy classes of chain maps; the
  quotient functor is `HomotopyCategory.quotient`.

* (Definition 1, Acyclic complex.) A complex `M` is *acyclic* if it is exact at
  every degree, i.e. all cohomology objects vanish. In Mathlib this is
  `HomologicalComplex.Acyclic M`, defined as `∀ i, M.ExactAt i`.

* (Definition 2, K-injective complex; Tag 070H.) A complex `I` is *K-injective*
  if for every acyclic complex `M` we have `Hom_{K(A)}(M, I) = 0`, equivalently
  every chain map `M ⟶ I` from an acyclic complex is null-homotopic (homotopic to
  the zero map). We take the "null-homotopic" formulation as the definition
  `IsKInjective` below, and record (theorem `isKInjective_iff_hom_homotopyCategory_zero`)
  that it is equivalent to the vanishing of `Hom` in `K(A)`.

* (Definition 3, Inverse system of complexes and its limit.) The inverse system,
  indexed by `1 ≤ 2 ≤ 3 ≤ ⋯` with transition maps going from larger to smaller
  index, is modelled as a functor `F : ℕᵒᵖ ⥤ CochainComplex A ℤ`. The transition
  map `p_n : I_{n+1} ⟶ I_n` is `F.map (homOfLE (Nat.le_succ n)).op`. The
  hypothesis that "the degreewise limits `lim_n Iₙ^m` exist" assembles to the
  statement that the limit of `F` in the category of complexes exists, modelled by
  the instance assumption `[HasLimit F]`; the limit complex is then `limit F` and
  comes with canonical projections `limit F ⟶ Iₙ`. (As noted in the source, given
  the degreewise limits the limit complex is automatically the limit of the
  inverse system of complexes.)

* (Definition 4, Split surjection.) A morphism `f : X ⟶ Y` is a *split surjection*
  if it admits a section `s : Y ⟶ X` with `f ∘ s = id`. In Mathlib this is
  `IsSplitEpi f`. Hypothesis (2) is degreewise: for each `n`, the chain map `p_n`
  is split epi in every degree `m` (the chosen sections need not be chain maps nor
  be compatible across degrees or across `n`).
-/

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

variable {A : Type*} [Category A] [Abelian A]

-- Main Definition(s)

/-! Definition 2 (Tag 070H) is Mathlib's `CochainComplex.IsKInjective`: for every acyclic `M`,
every chain map `M ⟶ I` is null-homotopic. It is stated there as a class with the same
quantifiers and the same conclusion `Nonempty (Homotopy f 0)`, so this file uses it directly. -/

/-- Correctness of `IsKInjective`: it is equivalent to the vanishing of all `Hom`
groups `Hom_{K(A)}(M, I)` for acyclic `M`, i.e. every chain map from an acyclic
complex becomes zero in the homotopy category `K(A)`. This is the precise content
of Definition 2. -/
theorem isKInjective_iff_hom_homotopyCategory_zero (I : CochainComplex A ℤ) :
    I.IsKInjective ↔
      ∀ (M : CochainComplex A ℤ), M.Acyclic → ∀ (f : M ⟶ I),
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f = 0 := by
  refine ⟨fun h M hM f => ?_, fun h => ⟨fun {M} f hM => ?_⟩⟩
  · exact (HomotopyCategory.quotient_map_eq_zero_iff f).2 (h.nonempty_homotopy_zero f hM)
  · exact (HomotopyCategory.quotient_map_eq_zero_iff f).1 (h M hM f)

-- Main Statement(s)

open CochainComplex.HomComplex

/-- **Helper (shift of acyclic is acyclic).** If `M` is acyclic then so is its `a`-fold shift
`M⟦a⟧`. Used in the crux lemma `coboundary_of_cocycle`, where the `(-1)`-cocycle `z` is
re-expressed as a chain map out of `M⟦1⟧`, which must again be acyclic to apply K-injectivity.
PROOF SKETCH: `HomologicalComplex.Acyclic` is `∀ i, ExactAt i`; the shift functor on cochain
complexes relabels degrees and is exact, so `ExactAt` is preserved. Look for a Mathlib lemma
relating `(M⟦a⟧).ExactAt i` to `M.ExactAt (i + a)` (e.g. via `CochainComplex.shiftFunctor`
and `HomologicalComplex.exactAt_shift` / `Acyclic.shift`); failing that, unfold `Acyclic`,
`ExactAt`, and transport exactness through the degreewise iso of the shift. -/
lemma acyclic_shiftFunctor (M : CochainComplex A ℤ) (hM : M.Acyclic) (a : ℤ) :
    ((shiftFunctor (CochainComplex A ℤ) a).obj M).Acyclic := by
  -- SANITY CHECK PASSED (lean-sanity-check: statement TRUE; no counterexample. Degree
  -- relabeling i ↦ i + a is a bijection on ℤ; homology unaffected by shift sign on
  -- differentials. Proved via `cohomologyShiftIso M i a`.)
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  -- `cohomologyShiftIso` lived in the Ch12/Sec14 draft, which section 12.14's promotion to
  -- `StacksCore/` removed; it was a thin wrapper on the Mathlib declaration tagged 011H there.
  exact IsZero.of_iso ((hM (i + a)).isZero_homology)
    ((CochainComplex.ShiftSequence.shiftIso A a i (i + a) (add_comm a i)).app M)

/-- A chain map from an acyclic complex to a K-injective complex is `δ` of a `(-1)`-cochain. -/
private lemma exists_cochain_delta_eq_ofHom (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (M : CochainComplex A ℤ) (hM : M.Acyclic) (f : M ⟶ I) :
    ∃ z : Cochain M I (-1), δ (-1) 0 z = Cochain.ofHom f := by
  obtain ⟨H⟩ := hI.nonempty_homotopy_zero f hM
  refine ⟨(Cochain.equivHomotopy f 0 H).1, ?_⟩
  have hp := (Cochain.equivHomotopy f 0 H).2
  simp only [Cochain.ofHom_zero, add_zero] at hp
  rw [← hp]

/-- **Crux of Tag 070L (step 3): cocycle ⇒ coboundary.** If `I` is K-injective and `M` is
acyclic, then every `(-1)`-cocycle `z` in the Hom-complex `Hom^•(M, I)` (i.e. `δ (-1) 0 z = 0`)
is a coboundary: there is a `(-2)`-cochain `w` with `δ (-2) (-1) w = z`. This is the vanishing
of `H^{-1}(Hom^•(M, I)) ≅ Hom_{K(A)}(M⟦1⟧, I)`.
PROOF SKETCH (cochain-API route, validated against the `CochainComplex.HomComplex` API):
1. `zs := z.leftShift 1 0 (by ring) : Cochain (M⟦1⟧) I 0`. Compute `δ 0 1 zs = 0` from
   `hz` via the shift δ-lemma (search `Cochain.δ_leftShift` / nearby; the closer reported a
   factor `(1).negOnePow • (δ (-1) 0 z).leftShift …`, which is `0` since `δ (-1) 0 z = 0`).
2. Form the cocycle `c := Cocycle.mk zs 1 (by ring) (this)` and `φ := c.homOf : M⟦1⟧ ⟶ I`,
   with `Cochain.ofHom φ = zs` (lemma `Cocycle.ofHom_homOf` / `homOf` simp lemma).
3. `M⟦1⟧` is acyclic by `acyclic_shiftFunctor M hM 1`; K-injectivity `hI` gives
   `H : Homotopy φ 0`. Via `Cochain.equivHomotopy`, `u := (equivHomotopy φ 0 H).1` satisfies
   `δ (-1) 0 u = Cochain.ofHom φ = zs`.
4. `w := u.leftUnshift (-2) (by ring) : Cochain M I (-2)`. Then `δ (-2) (-1) w = z`: use the
   unshift δ-lemma (`Cochain.δ_leftUnshift`) together with `leftUnshift_leftShift` to undo
   the shift on `zs` and recover `z` (watch the `negOnePow` sign; it cancels). -/
lemma coboundary_of_cocycle (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (M : CochainComplex A ℤ) (hM : M.Acyclic)
    (z : Cochain M I (-1)) (hz : δ (-1) 0 z = 0) :
    ∃ w : Cochain M I (-2), δ (-2) (-1) w = z := by
  -- Step 1: leftShift z by 1 to a degree-0 cochain on M⟦1⟧.
  set zs : Cochain ((shiftFunctor (CochainComplex A ℤ) (1 : ℤ)).obj M) I 0 :=
    z.leftShift 1 0 (by ring) with hzs
  -- Step 2: zs is a cocycle, δ 0 1 zs = 0.
  have hδzs : δ 0 1 zs = 0 := by
    rw [hzs, Cochain.δ_leftShift z 1 0 1 (by ring) 0 (by ring), hz]
    simp
  -- Step 3: package as a cocycle and get a chain map φ.
  let c : Cocycle ((shiftFunctor (CochainComplex A ℤ) (1 : ℤ)).obj M) I 0 :=
    Cocycle.mk zs 1 (by ring) hδzs
  let φ : (shiftFunctor (CochainComplex A ℤ) (1 : ℤ)).obj M ⟶ I := c.homOf
  have hφzs : Cochain.ofHom φ = zs := by
    have := Cocycle.cochain_ofHom_homOf_eq_coe c
    simp [φ, c]
  -- Step 4: M⟦1⟧ is acyclic, so K-injectivity gives a null-homotopy of φ.
  have hac := acyclic_shiftFunctor M hM 1
  -- Step 5: extract the cochain u with δ (-1) 0 u = zs.
  obtain ⟨u, hu⟩ := exists_cochain_delta_eq_ofHom I hI _ hac φ
  have hδu : δ (-1) 0 u = zs := hu.trans hφzs
  -- Step 6: unshift u back to a degree-(-2) cochain; the unshift δ-lemma introduces a
  -- sign `(1).negOnePow = -1`, so we negate to recover `z` exactly.
  refine ⟨-(u.leftUnshift (-2) (by ring)), ?_⟩
  have hδw : δ (-2) (-1) (u.leftUnshift (-2) (by ring)) = -z := by
    rw [Cochain.δ_leftUnshift u (-2) (by ring) (-1) 0 (by ring), hδu, hzs,
      Cochain.leftUnshift_leftShift z 1 0 (by ring)]
    simp
  rw [δ_neg, hδw, neg_neg]

/-- Given a tower `F` of K-injective complexes whose transition maps are degreewise split
epimorphisms, an acyclic complex `M` and a morphism `f : M ⟶ limit F`, there is a family of
cochains `H n : Cochain M (F.obj (op n)) (-1)` with `δ (-1) 0 (H n) = ofHom (f ≫ limit.π F (op n))`
whose members are compatible under composition with the transition maps of `F`.

The proof is an induction on `n`, the Mittag–Leffler step of Stacks 070L: a null-homotopy
`H'` of `f ≫ limit.π F (op (n+1))` differs from the image of `H n` by a cocycle, which is a
coboundary `δ w` by K-injectivity of `F.obj (op n)`; lifting `w` through the degreewise sections
of the transition map (the only use of the splitting hypothesis) corrects `H'` to `H (n+1)`. -/
lemma exists_compatible_cochain_family
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit F]
    (hKInj : ∀ n : ℕ, (F.obj (op n)).IsKInjective)
    (hSplit : ∀ (n : ℕ) (m : ℤ),
      IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f m))
    (M : CochainComplex A ℤ) (hM : M.Acyclic) (f : M ⟶ limit F) :
    ∃ H : (n : ℕ) → Cochain M (F.obj (op n)) (-1),
      (∀ n, δ (-1) 0 (H n) = Cochain.ofHom (f ≫ limit.π F (op n))) ∧
      (∀ n, (H (n + 1)).comp (Cochain.ofHom (F.map (homOfLE (Nat.le_succ n)).op)) (by ring)
        = H n) := by
  -- Helper: the inductive step. Given `Hn` null-homotopy cochain of `fₙ`, build `H_{n+1}`
  -- null-homotopy cochain of `f_{n+1}` compatible with `Hn` along the transition map.
  have step : ∀ (n : ℕ) (Hn : Cochain M (F.obj (op n)) (-1)),
      δ (-1) 0 Hn = Cochain.ofHom (f ≫ limit.π F (op n)) →
      ∃ Hs : Cochain M (F.obj (op (n+1))) (-1),
        δ (-1) 0 Hs = Cochain.ofHom (f ≫ limit.π F (op (n+1))) ∧
        Hs.comp (Cochain.ofHom (F.map (homOfLE (Nat.le_succ n)).op)) (by ring) = Hn := by
    intro n Hn hHn
    set p := F.map (homOfLE (Nat.le_succ n)).op with hp
    set fn := f ≫ limit.π F (op n) with hfn
    set fs := f ≫ limit.π F (op (n+1)) with hfs
    have hcone : fs ≫ p = fn := by
      rw [hfs, hp, hfn, Category.assoc, limit.w]
    obtain ⟨H', hH'⟩ : ∃ z : Cochain M (F.obj (op (n+1))) (-1), δ (-1) 0 z = Cochain.ofHom fs := by
      exact exists_cochain_delta_eq_ofHom _ (hKInj (n+1)) M hM fs
    set z : Cochain M (F.obj (op n)) (-1) := Hn - H'.comp (Cochain.ofHom p) (by ring) with hz
    have hδz : δ (-1) 0 z = 0 := by
      rw [hz, δ_sub, hHn, δ_comp_ofHom H' p 0, hH', ← Cochain.ofHom_comp, hcone, hfn]
      abel
    obtain ⟨w, hw⟩ := coboundary_of_cocycle (F.obj (op n)) (hKInj n) M hM z hδz
    let w' : Cochain M (F.obj (op (n+1))) (-2) := Cochain.mk (fun i j hij =>
      w.v i j hij ≫ (@section_ _ _ _ _ (p.f j) (hSplit n j)))
    have hw' : w'.comp (Cochain.ofHom p) (by ring) = w := by
      apply Cochain.ext
      intro i j hij
      rw [Cochain.comp_v w' (Cochain.ofHom p) (by ring) i j j hij (by ring)]
      simp only [w', Cochain.mk_v, Cochain.ofHom_v, Category.assoc]
      rw [show (@section_ _ _ _ _ (p.f j) (hSplit n j)) ≫ p.f j = 𝟙 _ from
        @IsSplitEpi.id _ _ _ _ (p.f j) (hSplit n j)]
      simp
    refine ⟨H' + δ (-2) (-1) w', ?_, ?_⟩
    · rw [δ_add, hH', δ_δ, add_zero]
    · rw [Cochain.add_comp, ← δ_comp_ofHom w' p (-1), hw', hw, hz]
      abel
  -- Base case: null-homotopy cochain of `f₀`.
  obtain ⟨H0, hH0⟩ : ∃ z : Cochain M (F.obj (op 0)) (-1),
      δ (-1) 0 z = Cochain.ofHom (f ≫ limit.π F (op 0)) := by
    exact exists_cochain_delta_eq_ofHom _ (hKInj 0) M hM _
  -- Choice function for the step.
  choose Hsucc hHsucc_δ hHsucc_compat using step
  -- Build the family by recursion, packaging the δ-property in a sigma.
  let seq : (n : ℕ) → { H : Cochain M (F.obj (op n)) (-1) //
      δ (-1) 0 H = Cochain.ofHom (f ≫ limit.π F (op n)) } :=
    fun n => Nat.rec ⟨H0, hH0⟩
      (fun n prev => ⟨Hsucc n prev.1 prev.2, hHsucc_δ n prev.1 prev.2⟩) n
  -- `seq (n+1) = ⟨Hsucc n (seq n).1 (seq n).2, _⟩` definitionally; compat from `hHsucc_compat`.
  exact ⟨fun n => (seq n).1, fun n => (seq n).2, fun n => hHsucc_compat n (seq n).1 (seq n).2⟩

/-- **Compatibility of `cylinder.desc` with postcomposition.** If two null-homotopies arise
from cochains `z₀, z₁` with `z₀.comp (ofHom p) = z₁` and `φ₀ ≫ p = φ₁`, then the descended
cylinder maps satisfy `cylinder.desc φ₀ 0 H₀ ≫ p = cylinder.desc φ₁ 0 H₁`.
PROOF SKETCH: `cylinder.desc` is built from `homotopyCofiber.desc` and is determined
degreewise by `φ₀` (on the `ι₀` summand), `φ₁` (`ι₁`), and the homotopy operator `z` (the
cross term). Reduce to a degreewise check (`HomologicalComplex.hom_ext` / `cylinder.ext` after
composing with the structure maps `ι₀, ι₁` and the homotopy), then use the explicit degreewise
formula for `cylinder.desc` together with `hz`, `hφ`, `hH₀`, `hH₁`. Alternatively prove the
naturality `cylinder.desc φ₀ φ₁ H ≫ p = cylinder.desc (φ₀≫p) (φ₁≫p) (H.compRight p)` first,
then show the two homotopies `H.compRight p` and `H₁` agree because their cochains agree
(`z₀.comp (ofHom p) = z₁`) via injectivity of `equivHomotopy`. -/
lemma cylinder_desc_postcomp_compat
    (M I J : CochainComplex A ℤ) (φ₀ : M ⟶ I) (φ₁ : M ⟶ J) (p : I ⟶ J)
    (z₀ : Cochain M I (-1)) (z₁ : Cochain M J (-1))
    (H₀ : Homotopy φ₀ 0) (H₁ : Homotopy φ₁ 0)
    (hz : z₀.comp (Cochain.ofHom p) (by ring) = z₁)
    (hφ : φ₀ ≫ p = φ₁)
    (hH₀ : (Cochain.equivHomotopy φ₀ 0 H₀).1 = z₀)
    (hH₁ : (Cochain.equivHomotopy φ₁ 0 H₁).1 = z₁) :
    cylinder.desc φ₀ 0 H₀ ≫ p = cylinder.desc φ₁ 0 H₁ := by
  -- SANITY CHECK PASSED (lean-sanity-check: statement TRUE; no counterexample. The cochain
  -- naturality `cochain(H.compRight p) = cochain(H).comp (ofHom p)` was machine-verified with
  -- no hidden sign/orientation error; `cylinder.desc` is determined degreewise by the cochain.)
  -- Step 1: naturality of cylinder.desc under postcomposition by p.
  have nat : cylinder.desc φ₀ 0 H₀ ≫ p
      = cylinder.desc (φ₀ ≫ p) ((0 : M ⟶ I) ≫ p) (H₀.compRight p) := by
    unfold HomologicalComplex.cylinder.desc
    ext j
    rw [HomologicalComplex.comp_f]
    apply homotopyCofiber.ext_from_X (biprod.lift (𝟙 M) (-𝟙 M)) (j+1) j (by simp
        [ComplexShape.up_Rel])
    · rw [← Category.assoc, homotopyCofiber.inlX_desc_f, homotopyCofiber.inlX_desc_f]
      simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.equivSubZero, Homotopy.compRight,
        Equiv.coe_fn_mk, Pi.zero_apply, zero_add]
    · rw [← Category.assoc, homotopyCofiber.inrX_desc_f, homotopyCofiber.inrX_desc_f,
        ← HomologicalComplex.comp_f]
      congr 1
      ext <;> simp
  rw [nat]
  -- Step 2: generalized congruence keyed on the underlying cochains.
  have desc_congr : ∀ (ψ₀ ψ₀' ψ₁ ψ₁' : M ⟶ J),
      ψ₀ = ψ₀' → ψ₁ = ψ₁' →
      ∀ (H : Homotopy ψ₀ ψ₁) (H' : Homotopy ψ₀' ψ₁'),
      (Cochain.equivHomotopy ψ₀ ψ₁ H).1 = (Cochain.equivHomotopy ψ₀' ψ₁' H').1 →
      cylinder.desc ψ₀ ψ₁ H = cylinder.desc ψ₀' ψ₁' H' := by
    intro ψ₀ ψ₀' ψ₁ ψ₁' h0 h1 H H' hc
    subst h0 h1
    rw [(Cochain.equivHomotopy ψ₀ ψ₁).injective (Subtype.ext hc)]
  -- Step 3: the cochain naturality fact `cochain(H₀.compRight p) = cochain(H₀).comp (ofHom p)`.
  have hcochain : (Cochain.equivHomotopy (φ₀ ≫ p) ((0:M⟶I) ≫ p) (H₀.compRight p)).1
      = ((Cochain.equivHomotopy φ₀ 0 H₀).1).comp (Cochain.ofHom p) (by ring) := by
    rw [Cochain.equivHomotopy_apply_coe, Cochain.equivHomotopy_apply_coe]
    apply Cochain.ext
    intro i j hij
    rw [Cochain.comp_v _ _ (by ring) i j j hij (by ring)]
    simp only [Cochain.ofHomotopy, Cochain.mk_v, Cochain.ofHom_v, Homotopy.compRight]
  -- Step 4: apply congruence.
  apply desc_congr _ _ _ _ hφ (by simp) (H₀.compRight p) H₁
  rw [hcochain, hH₀, hz, hH₁]

/-- **Crux of Tag 070L: the compatible family of null-homotopies (Mittag–Leffler step).**

Fix an acyclic complex `M` and a chain map `f : M ⟶ limit F`. Write `Iₙ = F.obj (op n)`,
`pₙ : I_{n+1} ⟶ Iₙ` for the transition maps and `fₙ = f ≫ limit.π F (op n)` for the
"components" of `f`, so that `f_{n+1} ≫ pₙ = fₙ` (the cone condition `limit.w`).

This lemma produces a **compatible family of chain maps** `g : ∀ n, M.cylinder ⟶ Iₙ`
(a cone over `F` with vertex `M.cylinder`) such that, for every `n`,
* `g (n+1) ≫ pₙ = g n`           (compatibility along the tower),
* `cylinder.ι₀ M ≫ g n = fₙ`     (the `ι₀`-end recovers `fₙ`),
* `cylinder.ι₁ M ≫ g n = 0`      (the `ι₁`-end is `0`).

Equivalently (via `cylinder.desc` / `homotopyCofiber.descEquiv`) it produces a family of
null-homotopies `Hₙ : Homotopy fₙ 0` with `g n = cylinder.desc fₙ 0 Hₙ`, compatible in the
sense that the homotopy operators satisfy `H_{n+1}.hom i j ≫ (pₙ).f j = Hₙ.hom i j`.

INFORMAL PROOF (rigorous; the Mittag–Leffler / "split tower" argument of Stacks 070L).

We build the family `gₙ`, equivalently the homotopies `Hₙ : Homotopy fₙ 0` with the
operator-compatibility `H_{n+1}.hom i j ≫ (pₙ).f j = Hₙ.hom i j`, by induction on `n`.
Throughout, for a degreewise split epi `q = (pₙ).f j` we write `s_j` for a chosen section
(`IsSplitEpi.section_`, satisfying `s_j ≫ q = 𝟙`); these sections are *not* assumed to be
chain maps nor compatible across degrees or across `n` — that is exactly hypothesis (2).

Key bookkeeping fact (used twice): for any operator `h i j : M.X i ⟶ X.X j`, the chain map
`Homotopy.nullHomotopicMap h : M ⟶ X` is the "differential of `h` in the Hom-complex"
`Hom^•(M, X)`; a homotopy `Homotopy φ 0` is precisely an operator `h` with
`Homotopy.nullHomotopicMap h = φ`, and `nullHomotopicMap` is additive and satisfies
`nullHomotopicMap (fun i j => h i j ≫ q.f j) = nullHomotopicMap h ≫ q` for a chain map `q`
(`Homotopy.nullHomotopicMap_comp`).

* Base case `n = 0`. Since `I₀` is K-injective (`hKInj 0`) and `M` is acyclic, the chain map
  `f₀ : M ⟶ I₀` is null-homotopic: choose `H₀ : Homotopy f₀ 0`, i.e. an operator with
  `nullHomotopicMap H₀.hom = f₀`. Set `g₀ := cylinder.desc f₀ 0 H₀`; then
  `ι₀ ≫ g₀ = f₀` and `ι₁ ≫ g₀ = 0` by `cylinder.ι₀_desc` / `cylinder.ι₁_desc`.

* Inductive step. Suppose `Hₙ : Homotopy fₙ 0` is given. We construct `H_{n+1}`.
  1. (K-injectivity of `I_{n+1}`.) `f_{n+1} : M ⟶ I_{n+1}` is null-homotopic, so choose
     `H' : Homotopy f_{n+1} 0`, i.e. `nullHomotopicMap H'.hom = f_{n+1}`.
  2. (Discrepancy cocycle.) Consider the operator
     `z i j := Hₙ.hom i j - (H'.hom i j ≫ (pₙ).f j) : M.X i ⟶ Iₙ.X j`.
     Then, using `nullHomotopicMap_comp` and the cone identity `f_{n+1} ≫ pₙ = fₙ`,
       `nullHomotopicMap z = nullHomotopicMap Hₙ.hom − nullHomotopicMap H'.hom ≫ pₙ`
                            `= fₙ − f_{n+1} ≫ pₙ = fₙ − fₙ = 0`.
     Thus `z` is a *cocycle* in `Hom^•(M, Iₙ)` (in degree `−1`): the chain map
     `nullHomotopicMap z` is literally `0`. Equivalently, `z` is the operator of a homotopy
     `0 ≃ 0` (`Homotopy.nullHomotopy z`, whose underlying map is `0`).
  3. (K-injectivity of `Iₙ` on a shift of `M`: cocycle ⇒ coboundary — the crucial use of
     hypothesis (1) at level `n`.) Because `M` is acyclic and `Iₙ` is K-injective, the
     cohomology `H^{-1}(Hom^•(M, Iₙ)) ≅ Hom_{K(A)}(M[1], Iₙ)` vanishes (`M[1]` is acyclic);
     hence the cocycle `z` is a coboundary: there is a degree `−2` operator
     `w i j : M.X i ⟶ Iₙ.X j` with `z = "d w"`, i.e. `Hₙ.hom − (H'.hom ≫ pₙ)` equals the
     operator obtained by applying the Hom-complex differential to `w`. (Concretely `w` is
     produced from a homotopy witnessing that the cocycle `z`, viewed as a chain map out of a
     shift of `M`, is null-homotopic.)
  4. (Lift the coboundary witness through the split epi.) Lift `w` *degreewise* through the
     sections: `w' i j := w i j ≫ s_j : M.X i ⟶ I_{n+1}.X j`, so that
     `w' i j ≫ (pₙ).f j = w i j` (since `s_j` is a section of `(pₙ).f j`). No chain-map
     property of `s_j` is needed because we will only apply the Hom-complex differential `d`
     to `w'`, and `d w'` is automatically a valid homotopy operator.
  5. (Corrected homotopy.) Set `H_{n+1}.hom := H'.hom + d w'` (i.e. `H_{n+1} := H'` corrected
     by the coboundary of `w'`). Then:
       - `H_{n+1}` is a genuine `Homotopy f_{n+1} 0`: `nullHomotopicMap (H'.hom + d w') =
         nullHomotopicMap H'.hom + nullHomotopicMap (d w') = f_{n+1} + 0 = f_{n+1}`, because a
         coboundary `d w'` satisfies `nullHomotopicMap (d w') = 0` (`d² = 0` in the
         Hom-complex; equivalently the comm condition holds tautologically for a coboundary).
       - Compatibility: applying `(- ≫ pₙ)` (postcomposition, a chain map, so it commutes with
         the Hom-complex differential via `nullHomotopicMap_comp`):
         `(d w') ≫ pₙ = d (w' ≫ pₙ) = d w` (degreewise `w' i j ≫ (pₙ).f j = w i j`), whence
         `H_{n+1}.hom (- ≫ pₙ) = H'.hom (- ≫ pₙ) + d w = H'.hom (- ≫ pₙ) + z
                               = H'.hom (- ≫ pₙ) + (Hₙ.hom − H'.hom (- ≫ pₙ)) = Hₙ.hom`,
         i.e. `H_{n+1}.hom i j ≫ (pₙ).f j = Hₙ.hom i j` for all `i, j`.
  Define `g (n+1) := cylinder.desc f_{n+1} 0 H_{n+1}`. The operator-compatibility
  `H_{n+1}.hom (- ≫ pₙ) = Hₙ.hom` translates, via the explicit degreewise formula for
  `cylinder.desc`, into the chain-map identity `g (n+1) ≫ pₙ = g n`; the `ι₀`/`ι₁` ends are
  `f_{n+1}` and `0` by `ι₀_desc` / `ι₁_desc`.

This completes the induction; the resulting `g` is the required compatible family. ∎

NOTE FOR THE FORMAL PHASE. The genuinely hard content is step 3 (cocycle ⇒ coboundary), which
is K-injectivity of `Iₙ` re-expressed as the vanishing of `H^{-1}(Hom^•(M, Iₙ))` for acyclic
`M`. It is convenient to first record, as a helper_070l lemma, the statement: *if `I` is
K-injective and `M` is acyclic, then for every operator `z : ∀ i j, M.X i ⟶ I.X j` with
`Homotopy.nullHomotopicMap z = 0` there exists an operator `w` with `z` equal to the
Hom-complex differential of `w`* (a "homotopy between the two trivial null-homotopies").
The remaining steps are additive/`nullHomotopicMap` bookkeeping plus `cylinder.desc`
computations, both of which are routine `simp`/`abel` arguments over the API probed above
(`Homotopy.nullHomotopicMap_comp`, `cylinder.ι₀_desc`, `cylinder.ι₁_desc`). -/
theorem exists_compatible_homotopy_family
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit F]
    (hKInj : ∀ n : ℕ, (F.obj (op n)).IsKInjective)
    (hSplit : ∀ (n : ℕ) (m : ℤ),
      IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f m))
    (M : CochainComplex A ℤ) (hM : M.Acyclic) (f : M ⟶ limit F) :
    ∃ g : (n : ℕ) → M.cylinder ⟶ F.obj (op n),
      (∀ n, g (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = g n) ∧
      (∀ n, cylinder.ι₀ M ≫ g n = f ≫ limit.π F (op n)) ∧
      (∀ n, cylinder.ι₁ M ≫ g n = 0) := by
  -- SANITY CHECK PASSED (lean-sanity-check: statement TRUE; the `split` hypothesis is
  -- load-bearing exactly at the coboundary-lift step; no degree/orientation error).
  -- Obtain the compatible family of homotopy operators (cochain language).
  obtain ⟨H, hHδ, hHcompat⟩ :=
    exists_compatible_cochain_family F hKInj hSplit M hM f
  -- Turn each operator into a genuine null-homotopy `Hₙ : Homotopy fₙ 0`.
  set fc : (n : ℕ) → (M ⟶ F.obj (op n)) := fun n => f ≫ limit.π F (op n) with hfc
  let homot : (n : ℕ) → Homotopy (fc n) 0 := fun n =>
    (Cochain.equivHomotopy (fc n) 0).symm ⟨H n, by rw [hHδ n]; simp [hfc]⟩
  -- The underlying cochain of `homot n` is exactly `H n`.
  have hHomot : ∀ n, (Cochain.equivHomotopy (fc n) 0 (homot n)).1 = H n := by
    intro n
    change (Cochain.equivHomotopy (fc n) 0 ((Cochain.equivHomotopy (fc n) 0).symm _)).1 = H n
    rw [Equiv.apply_symm_apply]
  -- The cone identity `f_{n+1} ≫ pₙ = fₙ` (`limit.w`).
  have hcone : ∀ n, fc (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op = fc n := by
    intro n
    simp only [hfc, Category.assoc, limit.w]
  -- The compatible family of cylinder maps.
  refine ⟨fun n => cylinder.desc (fc n) 0 (homot n), fun n => ?_, fun n => ?_, fun n => ?_⟩
  · -- compatibility `g (n+1) ≫ pₙ = g n`, via `cylinder_desc_postcomp_compat`.
    exact cylinder_desc_postcomp_compat M (F.obj (op (n + 1))) (F.obj (op n))
      (fc (n + 1)) (fc n) (F.map (homOfLE (Nat.le_succ n)).op)
      (H (n + 1)) (H n) (homot (n + 1)) (homot n)
      (hHcompat n) (hcone n) (hHomot (n + 1)) (hHomot n)
  · -- `ι₀`-end: recovers `fₙ`.
    simp [hfc, cylinder.ι₀_desc (fc n) 0 (homot n)]
  · -- `ι₁`-end: is `0`.
    simp [cylinder.ι₁_desc (fc n) 0 (homot n)]

/-- **Cylinder extension along the limit.** From the compatible family of cylinder maps
(`exists_compatible_homotopy_family`) we assemble, via the universal property of `limit F`
in the category of complexes (`NatTrans.ofOpSequence` to build the cone, then `limit.lift`),
a single chain map `g : M.cylinder ⟶ limit F` whose two ends recover `f` and `0`. -/
theorem exists_cylinder_extension_limit
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit F]
    (hKInj : ∀ n : ℕ, (F.obj (op n)).IsKInjective)
    (hSplit : ∀ (n : ℕ) (m : ℤ),
      IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f m))
    (M : CochainComplex A ℤ) (hM : M.Acyclic) (f : M ⟶ limit F) :
    ∃ G : M.cylinder ⟶ limit F,
      cylinder.ι₀ M ≫ G = f ∧ cylinder.ι₁ M ≫ G = 0 := by
  obtain ⟨g, hgcompat, hg0, hg1⟩ :=
    exists_compatible_homotopy_family F hKInj hSplit M hM f
  -- Build the cone over `F` with vertex `M.cylinder` from the successive-compatible family.
  let c : Cone F := Cone.mk M.cylinder (NatTrans.ofOpSequence g (by
    intro n
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    exact (hgcompat n).symm))
  refine ⟨limit.lift F c, ?_, ?_⟩
  · -- `ι₀ ≫ G = f`: check after composing with each `limit.π`.
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, limit.lift_π]
    change cylinder.ι₀ M ≫ c.π.app (op n) = _
    simp only [c, NatTrans.ofOpSequence_app]
    rw [hg0]
  · -- `ι₁ ≫ G = 0`: check after composing with each `limit.π`.
    apply limit.hom_ext
    rintro ⟨n⟩
    simp only [Category.assoc, limit.lift_π, zero_comp]
    change cylinder.ι₁ M ≫ c.π.app (op n) = _
    simp only [c, NatTrans.ofOpSequence_app]
    rw [hg1]

/-- **Stacks Tag 070L (Lemma 13.31.8).** Let `A` be an abelian category and let
`F : ℕᵒᵖ ⥤ CochainComplex A ℤ` be an inverse system of complexes (transition maps
go from larger to smaller index). Assume:
1. each complex `F.obj (op n)` is K-injective;
2. each transition map `F_{n+1} ⟶ F_n` is a split surjection in every degree `m`;
3. the limit complex `limit F` exists (the degreewise limits exist in `A`).
Then the limit complex `limit F` is K-injective.

The proof reduces (via `exists_cylinder_extension_limit`, then
`exists_compatible_homotopy_family`) to the Mittag–Leffler construction of a compatible
family of null-homotopies; the final step postcomposes the canonical cylinder homotopy
`cylinder.ι₀ ≃ cylinder.ι₁` with the assembled extension. -/
@[stacks 070L]
theorem isKInjective_limit_of_inverseSystem
    (F : ℕᵒᵖ ⥤ CochainComplex A ℤ) [HasLimit F]
    (hKInj : ∀ n : ℕ, (F.obj (op n)).IsKInjective)
    (hSplit : ∀ (n : ℕ) (m : ℤ),
      IsSplitEpi ((F.map (homOfLE (Nat.le_succ n)).op).f m)) :
    (limit F).IsKInjective := by
  -- For `ℤ`-indexed cochain complexes, every degree `j` has a predecessor in `up ℤ`, so the
  -- canonical homotopy `cylinder.ι₀ ≃ cylinder.ι₁` is available.
  have hc : ∀ (j : ℤ), ∃ (i : ℤ), (ComplexShape.up ℤ).Rel i j :=
    fun j => ⟨j - 1, by simp [ComplexShape.up_Rel]⟩
  refine ⟨fun {M} f hM => ?_⟩
  -- Reduce to building a chain map `M.cylinder ⟶ limit F` with the two prescribed ends.
  obtain ⟨G, hG0, hG1⟩ := exists_cylinder_extension_limit F hKInj hSplit M hM f
  -- Postcompose the canonical homotopy `ι₀ ≃ ι₁` with `G`; its ends are `f` and `0`.
  have H := (cylinder.homotopy₀₁ M hc).compRight G
  rw [hG0, hG1] at H
  exact ⟨H⟩

end

end
