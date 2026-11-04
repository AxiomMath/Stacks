module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.HomBicomplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The total complex of the Hom bicomplex computes `Ext`

Let `C` be an abelian category, let `K` be a cochain complex of `C` which is bounded above, and
let `I` be a bounded below cochain complex of `C`. The Hom bicomplex
`CochainComplex.homBicomplex K I` has `(p, q)` term `Hom_C(K⁻ᵖ, Iᑫ)`; its diagonals are finite,
so its total complex `⊕_{p + q = n} Hom_C(K⁻ᵖ, Iᑫ)` exists. Mathlib's
`CochainComplex.HomComplex K I` is the complex whose degree `n` term is the *product*
`∏_p Hom_C(Kᵖ, Iᵖ⁺ⁿ)` of all cochains of degree `n`. Under the two boundedness assumptions only
finitely many factors are nonzero, and the two complexes are isomorphic: that isomorphism is
`CochainComplex.HomBicomplex.totalIsoHomComplex`.

Combining it with Mathlib's identification of the cohomology of `HomComplex K I` with homotopy
classes of maps `K ⟶ I⟦n⟧`, and with [Stacks 06XR] (computation of `Ext` by an injective
resolution, `ExtByResolutions.ext_via_injective_resolution_bijective`), the degree `n` cohomology
of the total complex of `homBicomplex K I` is `Extⁿ(K, F)` when `I` is an injective resolution
of an object `F` placed in degree `0`. This is
`CochainComplex.homBicomplexTotalHomologyAddEquivExt`, the identification used in the
construction of the two spectral sequences of [Stacks 07AA].

## Main definitions

* `CochainComplex.HomBicomplex.sign`: the sign `(-1)^(a b + a (a + 1) / 2)` by which the two
  differential conventions differ.
* `CochainComplex.HomBicomplex.HasVanishingSummands`: the hypothesis that all summands of a
  diagonal outside a fixed finite set of first-degrees vanish.
* `CochainComplex.HomBicomplex.totalToHomComplexX`,
  `CochainComplex.HomBicomplex.homComplexXToTotalOfSupport` and
  `CochainComplex.HomBicomplex.homComplexXToTotal`: the degreewise comparison maps.
* `CochainComplex.HomBicomplex.totalIsoHomComplexOfSupport` and
  `CochainComplex.HomBicomplex.totalIsoHomComplex`: the comparison isomorphism of complexes,
  under vanishing summands and under the two boundedness hypotheses respectively.
* `CochainComplex.HomBicomplex.extAddEquivOfInjectiveResolution`: [Stacks 06XR] (1) upgraded from
  a bijection to an additive equivalence.

## Main results

* `CochainComplex.HomBicomplex.totalToHomComplexX_comm`: the degreewise comparison maps form a
  morphism of complexes.
* `CochainComplex.homBicomplexTotalHomologyAddEquivCohomologyClass`: the cohomology of the total
  Hom bicomplex is the group of cohomology classes of the Hom complex.
* `CochainComplex.homBicomplexTotalHomologyAddEquivExt`: the cohomology of the total Hom
  bicomplex of a bounded above complex and an injective resolution of an object is `Ext`.

## Implementation notes

**The sign is quadratic and is forced.** On the `(a, b)` summand the total complex differential
is `d₁ + (-1)^a d₂` (`HomologicalComplex₂.ιTotal_d_up_ℤ`, since `ε₁ = 1` and `ε₂ (a, b) = (-1)^a`
for the `TotalComplexShape` of `ComplexShape.up ℤ`), while the differential of
`HomComplex K I` is `d_I ∘ z + (-1)^(n+1) z ∘ d_K` (`CochainComplex.HomComplex.δ_v`). Matching
the two forces a sign `σ` with `σ (a, b + 1) = (-1)^a σ (a, b)` and
`σ (a + 1, b) = (-1)^(a + b + 1) σ (a, b)`; there is no solution with an exponent that is linear
or bilinear in `(a, b)`, and the general solution is `σ (a, b) = (-1)^(a b + a (a + 1) / 2)`
(`sign`), up to a global constant. The division by two is exact (`triangular_succ`).

**Universes.** `C : Type u` with `Category.{v} C`, and nothing is pinned: the value universe `v`
is only carried by the statements (`AddCommGrpCat.{v}` is where `preadditiveCoyoneda` lands) and
is never computed from them, so no `max` constraint arises. In particular the ringed-site
specialisation at `RingedSite.{u, u, u}` and `SheafOfModules.{u}` is an instance of the
statements here.

**The inverse comparison needs only finitely many nonzero summands.** The two boundedness
hypotheses enter only through `HasVanishingSummands`, so the inverse map and the comparison
isomorphism are stated for that hypothesis first and specialised afterwards. Boundedness above
of `K` alone already supplies it, with no hypothesis on `I`.

**No hypothesis is added.** `EnoughInjectives C` appears only where the chosen resolution
`CochainComplex.injectiveResolutionSingle` is used, and `HasDerivedCategory C` only where `Ext`
is mentioned; both are already needed to state the result. The boundedness of `K` is
`CochainComplex.minus` and that of `I` is the `boundedBelow` field of the resolution, exactly as
in `StacksFrontier.Algebra.Homology.HomBicomplex`.

**Spelling discipline.** The `(a, b)` term of `homBicomplex K I` is `Hom_C(K⁻ᵃ, Iᵇ)` only up to
the spelling `(preadditiveCoyonedaObj _).obj _`, which is definitionally but not syntactically
`K.X (-a) ⟶ I.X b`; `summandTo` and `summandFrom` are therefore `def`s with *ascribed* types, and
the arithmetic lemmas about them are stated for binders at the `K.X (-a) ⟶ I.X b` spelling and
applied at the crossing points only. For the same reason the comparison maps are never unfolded
by `rw`: `ιTotal_totalToHomComplexX` is the `rfl`-lemma used instead.

## References

* [Stacks, Tag 06XR](https://stacks.math.columbia.edu/tag/06XR)
* [Stacks, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
* [Stacks, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

namespace HomBicomplex

/-- `(-1)^(a (a + 1) / 2)`. -/
def triangularSign (a : ℤ) : ℤˣ := (a * (a + 1) / 2).negOnePow

/-- The triangular numbers satisfy `(a + 1) (a + 2) / 2 = a (a + 1) / 2 + (a + 1)` over `ℤ`,
with exact division. -/
lemma triangular_succ (a : ℤ) : (a + 1) * (a + 1 + 1) / 2 = a * (a + 1) / 2 + (a + 1) := by
  have h2 : a * (a + 1) / 2 * 2 = a * (a + 1) :=
    Int.ediv_mul_cancel (Int.even_mul_succ_self a).two_dvd
  have key : (a + 1) * (a + 1 + 1) = (a * (a + 1) / 2 + (a + 1)) * 2 := by linear_combination -h2
  rw [key, Int.mul_ediv_cancel _ (by norm_num)]

/-- `triangularSign (a + 1) = (-1)^(a + 1) * triangularSign a`. -/
lemma triangularSign_succ (a : ℤ) :
    triangularSign (a + 1) = (a + 1).negOnePow * triangularSign a := by
  rw [triangularSign, triangularSign, triangular_succ, Int.negOnePow_add, mul_comm]

/-- `(-1)^(a b + a (a + 1) / 2)`. -/
def sign (a b : ℤ) : ℤˣ := (a * b).negOnePow * triangularSign a

/-- `sign a (b + 1) = (-1)^a * sign a b`. -/
lemma sign_succ_right (a b : ℤ) : sign a (b + 1) = a.negOnePow * sign a b := by
  rw [sign, sign, show a * (b + 1) = a * b + a by ring, Int.negOnePow_add]
  ac_rfl

/-- `sign (a + 1) b = (-1)^(a + b + 1) * sign a b`. -/
lemma sign_succ_left (a b : ℤ) : sign (a + 1) b = (a + b + 1).negOnePow * sign a b := by
  simp only [sign, triangularSign_succ, show (a + 1) * b = a * b + b by ring, Int.negOnePow_add]
  ac_rfl

variable {C : Type u} [Category.{v} C] [Abelian C] (K I : CochainComplex C ℤ)

open HomComplex

/-- `Cochain.single` is additive in the morphism it is built from. -/
lemma single_add {p q : ℤ} (f g : K.X p ⟶ I.X q) (n : ℤ) :
    Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

/-- `Cochain.single`, as an additive map. -/
def singleAddHom {p q : ℤ} (n : ℤ) : (K.X p ⟶ I.X q) →+ Cochain K I n where
  toFun f := Cochain.single f n
  map_zero' := Cochain.single_zero K I p q n
  map_add' f g := single_add K I f g n

/-- `Cochain.single` commutes with multiplication by a unit of `ℤ`. -/
lemma single_units_smul {p q : ℤ} (u : ℤˣ) (f : K.X p ⟶ I.X q) (n : ℤ) :
    Cochain.single (u • f) n = u • Cochain.single f n := by
  rw [Units.smul_def, Units.smul_def]
  exact (singleAddHom K I n).map_zsmul (u : ℤ) f

/-- Evaluation of a cochain at a pair of degrees, as an additive map. -/
def vAddHom (p q n : ℤ) (h : p + n = q) : Cochain K I n →+ (K.X p ⟶ I.X q) where
  toFun z := z.v p q h
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The sign-twisted inclusion of the `(a, b)` summand of the Hom bicomplex into the degree `n`
term of the Hom complex. -/
def signedSingleAddHom (a b n : ℤ) : (K.X (-a) ⟶ I.X b) →+ Cochain K I n where
  toFun φ := sign a b • Cochain.single φ n
  map_zero' := by rw [Cochain.single_zero, smul_zero]
  map_add' φ ψ := by rw [single_add, smul_add]

/-- The sign-twisted projection of the degree `n` term of the Hom complex to the `(p, n - p)`
summand of the Hom bicomplex. -/
def signedEvalAddHom (p n : ℤ) : Cochain K I n →+ (K.X (-p) ⟶ I.X (n - p)) where
  toFun z := (sign p (n - p))⁻¹ • z.v (-p) (n - p) (by ring)
  map_zero' := by simp
  map_add' z w := by rw [Cochain.add_v, smul_add]

/-- The signed projection to the `(p, n - p)` summand is a left inverse of the signed inclusion
of that summand. -/
lemma signedEvalAddHom_signedSingleAddHom (p n : ℤ) (φ : K.X (-p) ⟶ I.X (n - p)) :
    signedEvalAddHom K I p n (signedSingleAddHom K I p (n - p) n φ) = φ := by
  show (sign p (n - p))⁻¹ • (sign p (n - p) • Cochain.single φ n).v (-p) (n - p) (by ring) = φ
  rw [Cochain.units_smul_v, Cochain.single_v, smul_smul, inv_mul_cancel, one_smul]

/-- The signed projection to the `(s, n - s)` summand vanishes on the signed inclusion of the
`(p, n - p)` summand for `s ≠ p`. -/
lemma signedEvalAddHom_signedSingleAddHom_of_ne (p s n : ℤ) (hps : s ≠ p)
    (φ : K.X (-p) ⟶ I.X (n - p)) :
    signedEvalAddHom K I s n (signedSingleAddHom K I p (n - p) n φ) = 0 := by
  show (sign s (n - s))⁻¹ • (sign p (n - p) • Cochain.single φ n).v (-s) (n - s) (by ring) = 0
  rw [Cochain.units_smul_v,
    Cochain.single_v_eq_zero φ n (-s) (n - s) (by ring) (by omega), smul_zero, smul_zero]

/-- Projecting a cochain to the `(p, n - p)` summand and including it back gives the `single`
cochain of its `(-p, n - p)` component. -/
lemma signedSingleAddHom_signedEvalAddHom (p n : ℤ) (z : Cochain K I n) :
    signedSingleAddHom K I p (n - p) n (signedEvalAddHom K I p n z) =
      Cochain.single (z.v (-p) (n - p) (by ring)) n := by
  show sign p (n - p) • Cochain.single ((sign p (n - p))⁻¹ • _) n = _
  rw [single_units_smul, smul_smul, mul_inv_cancel, one_smul]

/-- The `(a, b)` summand of the degreewise comparison map. -/
noncomputable def summandTo (a b n : ℤ) :
    ((homBicomplex K I).X a).X b ⟶ (HomComplex K I).X n :=
  AddCommGrpCat.ofHom (signedSingleAddHom K I a b n)

/-- The `(p, n - p)` summand of the degreewise inverse comparison map. -/
noncomputable def summandFrom (p n : ℤ) :
    (HomComplex K I).X n ⟶ ((homBicomplex K I).X p).X (n - p) :=
  AddCommGrpCat.ofHom (signedEvalAddHom K I p n)

/-- `summandFrom K I p n` is a left inverse of `summandTo K I p (n - p) n`. -/
lemma summandTo_summandFrom (p n : ℤ) :
    summandTo K I p (n - p) n ≫ summandFrom K I p n =
      𝟙 (((homBicomplex K I).X p).X (n - p)) := by
  ext φ
  exact signedEvalAddHom_signedSingleAddHom K I p n φ

/-- For `s ≠ p`, the composite of `summandTo K I p (n - p) n` and `summandFrom K I s n` is
zero. -/
lemma summandTo_summandFrom_of_ne (p s n : ℤ) (hps : s ≠ p) :
    summandTo K I p (n - p) n ≫ summandFrom K I s n = 0 := by
  ext φ
  exact signedEvalAddHom_signedSingleAddHom_of_ne K I p s n hps φ

/-- For `a + b = n`, the Hom complex differential of the signed `single` cochain of
`φ : K⁻ᵃ ⟶ Iᵇ` is the sum of the signed `single` cochains of `d_K ≫ φ` and `(-1)^a (φ ≫ d_I)`,
matching the total complex differential. -/
lemma signedSingleAddHom_comm (a b n : ℤ) (hab : a + b = n) (φ : K.X (-a) ⟶ I.X b) :
    δ n (n + 1) (sign a b • Cochain.single φ n)
      = sign (a + 1) b • Cochain.single (K.d (-(a + 1)) (-a) ≫ φ) (n + 1)
        + a.negOnePow • (sign a (b + 1) • Cochain.single (φ ≫ I.d b (b + 1)) (n + 1)) := by
  rw [δ_units_smul, Cochain.δ_single φ n (n + 1) rfl (-(a + 1)) (b + 1) (by ring) rfl,
    sign_succ_left, sign_succ_right, smul_add, smul_smul, smul_smul,
    hab, ← mul_assoc, Int.units_mul_self, one_mul,
    mul_comm (sign a b) ((n + 1).negOnePow),
    add_comm (sign a b • Cochain.single (φ ≫ I.d b (b + 1)) (n + 1))]

/-- A finite sum of morphisms of abelian groups, evaluated at an element. -/
lemma finsetSum_apply {M N : AddCommGrpCat.{v}} {J : Type*} (s : Finset J) (f : J → (M ⟶ N))
    (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  have h : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom := map_sum AddCommGrpCat.homAddEquiv f s
  show (∑ i ∈ s, f i).hom x = _
  rw [h, AddMonoidHom.finsetSum_apply]

/-- A finite sum of cochains, evaluated at a pair of degrees. -/
lemma sum_v {J : Type*} (s : Finset J) (n : ℤ) (f : J → Cochain K I n) (p q : ℤ)
    (h : p + n = q) : (∑ i ∈ s, f i).v p q h = ∑ i ∈ s, (f i).v p q h :=
  map_sum (vAddHom K I p q n h) f s

/-- For `K` bounded above by `a` and `I` bounded below by `b`, every morphism
`K⁻ᵖ ⟶ Iⁿ⁻ᵖ` with `p ∉ [-a, n - b]` is zero. -/
lemma eq_zero_of_notMem (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b] (n p : ℤ)
    (hp : p ∉ Finset.Icc (-a) (n - b)) (f : K.X (-p) ⟶ I.X (n - p)) : f = 0 := by
  simp only [Finset.mem_Icc, not_and, not_le] at hp
  rcases lt_or_ge p (-a) with h | h
  · exact (isZero_of_isStrictlyLE K a (-p) (by omega)).eq_of_src _ _
  · have h2 := hp h
    exact (isZero_of_isStrictlyGE I b (n - p) (by omega)).eq_of_tgt _ _

/-- The hypothesis under which the degree-`n` comparison between the total Hom bicomplex and
the Hom complex is an isomorphism: all the summands outside the finite set `s` of
first-degrees vanish. It holds when `K` is bounded above by `a` and `I` bounded below by `b`,
with `s = Finset.Icc (-a) (n - b)` (`eq_zero_of_notMem`), and it holds for every `n` with `s`
the support of `K` reflected, with no hypothesis on `I` at all. -/
def HasVanishingSummands (s : Finset ℤ) (n : ℤ) : Prop :=
  ∀ p ∉ s, ∀ f : K.X (-p) ⟶ I.X (n - p), f = 0

/-- A complex vanishing outside the reflection of `s` has vanishing summands in every
degree. -/
lemma hasVanishingSummands_of_isZero_left {s : Finset ℤ}
    (hK : ∀ p ∉ s, IsZero (K.X (-p))) (n : ℤ) : HasVanishingSummands K I s n :=
  fun p hp f => (hK p hp).eq_of_src f 0

/-- Under vanishing summands, the `(p, n - p)` term of the Hom bicomplex is zero for `p`
outside `s`. -/
lemma isZero_summand_of_hasVanishingSummands {s : Finset ℤ} {n : ℤ}
    (hs : HasVanishingSummands K I s n) {p : ℤ} (hp : p ∉ s) :
    IsZero (((homBicomplex K I).X p).X (n - p)) := by
  have : Subsingleton (((homBicomplex K I).X p).X (n - p)) :=
    ⟨fun a b => (hs p hp a).trans (hs p hp b).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- For `K` bounded above by `a` and `I` bounded below by `b`, the `(p, n - p)` term of the Hom
bicomplex is zero for `p ∉ [-a, n - b]`. -/
lemma isZero_summand_of_notMem (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b] (n p : ℤ)
    (hp : p ∉ Finset.Icc (-a) (n - b)) :
    IsZero (((homBicomplex K I).X p).X (n - p)) :=
  isZero_summand_of_hasVanishingSummands K I (eq_zero_of_notMem K I a b n) hp

/-- Under vanishing summands, a cochain of degree `n` is the sum of the `single` cochains of
its components indexed by `s`. -/
lemma sum_single_v_eq_of_hasVanishingSummands {s : Finset ℤ} {n : ℤ}
    (hs : HasVanishingSummands K I s n) (z : Cochain K I n) :
    ∑ p ∈ s, Cochain.single (z.v (-p) (n - p) (by ring)) n = z := by
  refine Cochain.ext _ _ fun p' q' h => ?_
  obtain ⟨p, rfl⟩ : ∃ p, p' = -p := ⟨-p', by ring⟩
  obtain rfl : q' = n - p := by omega
  rw [sum_v, Finset.sum_eq_single p
    (fun t _ _ => Cochain.single_v_eq_zero _ n (-p) (n - p) h (by omega))
    (fun hp => by rw [Cochain.single_v]; exact hs p hp _), Cochain.single_v]

/-- For `K` bounded above by `a` and `I` bounded below by `b`, a cochain of degree `n` is the
sum of the `single` cochains of its finitely many possibly nonzero components. -/
lemma sum_single_v_eq (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b] (n : ℤ)
    (z : Cochain K I n) :
    ∑ p ∈ Finset.Icc (-a) (n - b), Cochain.single (z.v (-p) (n - p) (by ring)) n = z :=
  sum_single_v_eq_of_hasVanishingSummands K I (eq_zero_of_notMem K I a b n) z

/-- `summandFrom` followed by `summandTo` sends a cochain to the `single` cochain of its
`(-p, n - p)` component. -/
lemma summandFrom_summandTo_apply (p n : ℤ) (z : Cochain K I n) :
    (summandFrom K I p n ≫ summandTo K I p (n - p) n) z =
      Cochain.single (z.v (-p) (n - p) (by ring)) n :=
  signedSingleAddHom_signedEvalAddHom K I p n z

variable [(homBicomplex K I).HasTotal (ComplexShape.up ℤ)]

/-- The degree `n` part of the comparison map from the total Hom bicomplex to the Hom complex. -/
noncomputable def totalToHomComplexX (n : ℤ) :
    ((homBicomplex K I).total (ComplexShape.up ℤ)).X n ⟶ (HomComplex K I).X n :=
  (homBicomplex K I).totalDesc (fun a b _ => summandTo K I a b n)

/-- The restriction of `totalToHomComplexX K I n` to the `(a, b)` summand is
`summandTo K I a b n`. -/
@[reassoc]
lemma ιTotal_totalToHomComplexX (a b n : ℤ)
    (hab : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n) :
    (homBicomplex K I).ιTotal (ComplexShape.up ℤ) a b n hab ≫ totalToHomComplexX K I n =
      summandTo K I a b n :=
  HomologicalComplex₂.ι_totalDesc _ _ a b hab

/-- The degreewise comparison maps commute with the differentials of the total complex and of
the Hom complex. -/
lemma totalToHomComplexX_comm (n : ℤ) :
    totalToHomComplexX K I n ≫ (HomComplex K I).d n (n + 1) =
      ((homBicomplex K I).total (ComplexShape.up ℤ)).d n (n + 1) ≫
        totalToHomComplexX K I (n + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b hab
  simp only [ComplexShape.π_def] at hab
  rw [← Category.assoc, ιTotal_totalToHomComplexX, ← Category.assoc,
    HomologicalComplex₂.ιTotal_d_up_ℤ (homBicomplex K I) a b n hab,
    Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
    ιTotal_totalToHomComplexX, ιTotal_totalToHomComplexX]
  ext φ
  exact signedSingleAddHom_comm K I a b n hab φ

/-- The comparison morphism of complexes from the total Hom bicomplex to the Hom complex. -/
noncomputable def totalToHomComplex :
    (homBicomplex K I).total (ComplexShape.up ℤ) ⟶ HomComplex K I where
  f := totalToHomComplexX K I
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    exact totalToHomComplexX_comm K I n

/-- The degree `n` component of `totalToHomComplex K I` is `totalToHomComplexX K I n`. -/
@[simp]
lemma totalToHomComplex_f (n : ℤ) :
    (totalToHomComplex K I).f n = totalToHomComplexX K I n :=
  rfl

/-- The degree `n` part of the inverse comparison map, assembled from the summands indexed by
a finite set `s` of first-degrees. -/
noncomputable def homComplexXToTotalOfSupport (s : Finset ℤ) (n : ℤ) :
    (HomComplex K I).X n ⟶ ((homBicomplex K I).total (ComplexShape.up ℤ)).X n :=
  ∑ p ∈ s, summandFrom K I p n ≫
    (homBicomplex K I).ιTotal (ComplexShape.up ℤ) p (n - p) n (by simp [ComplexShape.π_def])

/-- Under vanishing summands outside `s`, `homComplexXToTotalOfSupport K I s n` is a left
inverse of `totalToHomComplexX K I n`. -/
lemma totalToHomComplexX_homComplexXToTotalOfSupport {s : Finset ℤ} {n : ℤ}
    (hs : HasVanishingSummands K I s n) :
    totalToHomComplexX K I n ≫ homComplexXToTotalOfSupport K I s n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  obtain rfl : q = n - p := by omega
  rw [← Category.assoc, ιTotal_totalToHomComplexX, Category.comp_id]
  rw [homComplexXToTotalOfSupport, Preadditive.comp_sum, Finset.sum_eq_single p
    (fun t _ htp => by
      rw [← Category.assoc, summandTo_summandFrom_of_ne K I p t n htp, Limits.zero_comp])
    (fun hp => (isZero_summand_of_hasVanishingSummands K I hs hp).eq_of_src _ _),
    ← Category.assoc, summandTo_summandFrom, Category.id_comp]

/-- Under vanishing summands outside `s`, `homComplexXToTotalOfSupport K I s n` is a right
inverse of `totalToHomComplexX K I n`. -/
lemma homComplexXToTotalOfSupport_totalToHomComplexX {s : Finset ℤ} {n : ℤ}
    (hs : HasVanishingSummands K I s n) :
    homComplexXToTotalOfSupport K I s n ≫ totalToHomComplexX K I n = 𝟙 _ := by
  have hsum : homComplexXToTotalOfSupport K I s n ≫ totalToHomComplexX K I n
      = ∑ p ∈ s, summandFrom K I p n ≫ summandTo K I p (n - p) n := by
    rw [homComplexXToTotalOfSupport, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun p _ => by rw [Category.assoc, ιTotal_totalToHomComplexX]
  rw [hsum]
  refine ConcreteCategory.hom_ext _ _ fun z => ?_
  rw [ConcreteCategory.id_apply, finsetSum_apply,
    Finset.sum_congr rfl fun p _ => summandFrom_summandTo_apply K I p n z]
  exact sum_single_v_eq_of_hasVanishingSummands K I hs z

/-- The comparison isomorphism between the total complex of the Hom bicomplex and the Hom
complex, whenever all summands outside a fixed finite set of first-degrees vanish. -/
noncomputable def totalIsoHomComplexOfSupport (s : Finset ℤ)
    (hs : ∀ n, HasVanishingSummands K I s n) :
    (homBicomplex K I).total (ComplexShape.up ℤ) ≅ HomComplex K I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := totalToHomComplexX K I n
        inv := homComplexXToTotalOfSupport K I s n
        hom_inv_id := totalToHomComplexX_homComplexXToTotalOfSupport K I (hs n)
        inv_hom_id := homComplexXToTotalOfSupport_totalToHomComplexX K I (hs n) })
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact totalToHomComplexX_comm K I i)

/-- The forward map of `totalIsoHomComplexOfSupport K I s hs` is `totalToHomComplex K I`. -/
@[simp]
lemma totalIsoHomComplexOfSupport_hom (s : Finset ℤ)
    (hs : ∀ n, HasVanishingSummands K I s n) :
    (totalIsoHomComplexOfSupport K I s hs).hom = totalToHomComplex K I :=
  rfl

/-- The degree `n` part of the inverse comparison map, for `K` bounded above by `a` and `I`
bounded below by `b`. -/
noncomputable def homComplexXToTotal (a b n : ℤ) :
    (HomComplex K I).X n ⟶ ((homBicomplex K I).total (ComplexShape.up ℤ)).X n :=
  homComplexXToTotalOfSupport K I (Finset.Icc (-a) (n - b)) n

/-- For `K` bounded above by `a` and `I` bounded below by `b`, `homComplexXToTotal K I a b n`
is a left inverse of `totalToHomComplexX K I n`. -/
lemma totalToHomComplexX_homComplexXToTotal (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b]
    (n : ℤ) : totalToHomComplexX K I n ≫ homComplexXToTotal K I a b n = 𝟙 _ :=
  totalToHomComplexX_homComplexXToTotalOfSupport K I (eq_zero_of_notMem K I a b n)

/-- For `K` bounded above by `a` and `I` bounded below by `b`, `homComplexXToTotal K I a b n`
is a right inverse of `totalToHomComplexX K I n`. -/
lemma homComplexXToTotal_totalToHomComplexX (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b]
    (n : ℤ) : homComplexXToTotal K I a b n ≫ totalToHomComplexX K I n = 𝟙 _ :=
  homComplexXToTotalOfSupport_totalToHomComplexX K I (eq_zero_of_notMem K I a b n)

/-- The comparison isomorphism between the total complex of the Hom bicomplex and the Hom
complex, for `K` bounded above by `a` and `I` bounded below by `b`. -/
noncomputable def totalIsoHomComplex (a b : ℤ) [K.IsStrictlyLE a] [I.IsStrictlyGE b] :
    (homBicomplex K I).total (ComplexShape.up ℤ) ≅ HomComplex K I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := totalToHomComplexX K I n
        inv := homComplexXToTotal K I a b n
        hom_inv_id := totalToHomComplexX_homComplexXToTotal K I a b n
        inv_hom_id := homComplexXToTotal_totalToHomComplexX K I a b n })
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact totalToHomComplexX_comm K I i)

/-- The cohomology of the total Hom bicomplex is the group of cohomology classes of the Hom
complex, for `K` bounded above by `a` and `I` bounded below by `b`. -/
noncomputable def totalHomologyAddEquivCohomologyClass (a b : ℤ)
    [K.IsStrictlyLE a] [I.IsStrictlyGE b] (n : ℤ) :
    (((homBicomplex K I).total (ComplexShape.up ℤ)).homology n) ≃+
      HomComplex.CohomologyClass K I n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n).mapIso
      (totalIsoHomComplex K I a b)).addCommGroupIsoToAddEquiv.trans
    (HomComplex.homologyAddEquiv K I n)

end HomBicomplex

/-- The cohomology of the total Hom bicomplex of a bounded above complex `K` and a bounded below
complex `I` is the group of degree `n` cohomology classes of the Hom complex. -/
noncomputable def homBicomplexTotalHomologyAddEquivCohomologyClass
    {C : Type u} [Category.{v} C] [Abelian C] (K I : CochainComplex C ℤ)
    (hK : CochainComplex.minus C K) (hI : CochainComplex.plus C I) (n : ℤ) :
    (homBicomplexTotal K I hK hI).homology n ≃+ HomComplex.CohomologyClass K I n :=
  let : K.IsStrictlyLE ((CochainComplex.minus_iff K).1 hK).choose :=
    ((CochainComplex.minus_iff K).1 hK).choose_spec
  let : I.IsStrictlyGE ((CochainComplex.plus_iff C I).1 hI).choose :=
    ((CochainComplex.plus_iff C I).1 hI).choose_spec
  let : (homBicomplex K I).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ _ (homBicomplex_finite_diagonals K I hK hI)
  HomBicomplex.totalHomologyAddEquivCohomologyClass K I
    ((CochainComplex.minus_iff K).1 hK).choose ((CochainComplex.plus_iff C I).1 hI).choose n

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace HomBicomplex

/-- Postcomposition with an isomorphism, as an additive equivalence. -/
@[simps]
def postcompAddEquiv {D : Type*} [Category D] [Preadditive D] {X Y Z : D} (e : Y ≅ Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun g := g ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := Preadditive.add_comp _ _ _ _ _ _

variable [HasDerivedCategory C]

/-- `ExtByResolutions.canMapOfInjectiveResolution` is additive. -/
noncomputable def canAddHom (X Y J : CochainComplex C ℤ) (i : ℤ) (f : Y ⟶ J) [QuasiIso f] :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J)⟦i⟧) →+
      (DerivedCategory.Q.obj X ⟶ (DerivedCategory.Q.obj Y)⟦i⟧) where
  toFun := ExtByResolutions.canMapOfInjectiveResolution X Y J i f
  map_zero' := by
    simp only [ExtByResolutions.canMapOfInjectiveResolution, CategoryTheory.Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  map_add' α β := by
    simp only [ExtByResolutions.canMapOfInjectiveResolution, CategoryTheory.Functor.map_add,
      Preadditive.add_comp, Preadditive.comp_add]

/-- The identification of `Ext` with homotopy classes of maps into an injective resolution,
as an additive equivalence. -/
noncomputable def extAddEquivOfInjectiveResolution (X Y J : CochainComplex C ℤ) (i : ℤ)
    {f : Y ⟶ J} (hf : ExtByResolutions.IsInjectiveResolution f) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj J)⟦i⟧) ≃+
      (DerivedCategory.Ext (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj Y) i) :=
  have := hf.quasiIso
  AddEquiv.ofBijective (canAddHom X Y J i f)
    (ExtByResolutions.ext_via_injective_resolution_bijective X Y J i hf)

omit [HasDerivedCategory C] in
/-- The chosen injective resolution `injectiveResolutionSingle F` of an object `F` is an
injective resolution in the sense of `ExtByResolutions.IsInjectiveResolution`. -/
@[sga "2 VIII 1.4" "special case"]
lemma isInjectiveResolution_injectiveResolutionSingle [EnoughInjectives C] (F : C) :
    ExtByResolutions.IsInjectiveResolution (injectiveResolutionSingle F).ι where
  quasiIso := (injectiveResolutionSingle F).quasiIso
  bddBelow := (plus_iff C _).1 (injectiveResolutionSingle F).boundedBelow
  injective := (injectiveResolutionSingle F).injective

end HomBicomplex

/-- **The total Hom bicomplex computes `Ext`.** For a bounded above cochain complex `K` of an
abelian category with enough injectives and an object `F`, the degree `n` cohomology of the
total complex of the Hom bicomplex of `K` and the chosen injective resolution of `F` placed in
degree `0` is the group `Extⁿ(K, F)` computed in the derived category. -/
noncomputable def homBicomplexTotalHomologyAddEquivExt [HasDerivedCategory C]
    [EnoughInjectives C] (K : CochainComplex C ℤ) (F : C) (hK : CochainComplex.minus C K)
    (n : ℤ) :
    (homBicomplexTotal K (injectiveResolutionSingle F).cocomplex hK
        (injectiveResolutionSingle F).boundedBelow).homology n ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj F)) n :=
  (homBicomplexTotalHomologyAddEquivCohomologyClass K _ hK _ n).trans <|
    HomComplex.CohomologyClass.homAddEquiv.trans <|
      (HomBicomplex.postcompAddEquiv
          (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app
            (injectiveResolutionSingle F).cocomplex)).trans <|
        HomBicomplex.extAddEquivOfInjectiveResolution K _ _ n
          (HomBicomplex.isInjectiveResolution_injectiveResolutionSingle F)

end Ext

end CochainComplex
