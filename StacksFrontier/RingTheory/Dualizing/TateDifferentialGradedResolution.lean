module

public import StacksFrontier.Algebra.DGA.CohomologicalRegrading
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Existence
public import StacksFrontier.RingTheory.Dualizing.DifferentialGradedResolution

/-!
# A nonnegatively graded resolution as a differential graded resolution

A Tate resolution of a commutative `R`-algebra `S` is a nonnegatively graded divided power
differential graded algebra `A` whose differential lowers degrees by one, together with an
augmentation `ε : A → S` whose exactness is recorded elementwise: `ε` kills the positive-degree
part and every boundary, a degree-zero element killed by `ε` is the boundary of a degree-one
element, and the complex is exact in every positive degree.

Reading the homological degree `k` in cohomological degree `-k` turns such an algebra into an
object of `DifferentialGradedAlgebra`, which is what
`DividedPowers.TateResolution.regradedDifferentialGradedAlgebra` does. This file promotes the
augmentation to a homomorphism of differential graded algebras into `S` placed in degree zero,
shows that the four elementary exactness conditions say exactly that it is an isomorphism on
cohomology, and assembles the data of Situation 0BZB, `Dualizing.DGAResolution`.

## Main definitions

* `DividedPowers.TateResolution.regradedAugmentationHom`: the augmentation, as a homomorphism
  from the regraded algebra to `S` concentrated in degree zero.
* `DividedPowers.TateResolution.dgaResolutionOfAugmentation`: the resulting
  `Dualizing.DGAResolution`, the data of Situation 0BZB.
* `DividedPowers.TateResolution.Resolution.regradedAlgebra` and
  `DividedPowers.TateResolution.Resolution.toDGAResolution`: the same for a bundled
  `DividedPowers.TateResolution.Resolution`, whose instances are fields rather than instance
  arguments.

## Main results

* `DifferentialGradedAlgebra.subsingleton_cohomology_of_grading_eq_bot` and
  `DifferentialGradedAlgebra.subsingleton_cohomology_of_exact`: the two ways a differential
  graded algebra can have no cohomology in a given degree.
* `DividedPowers.TateResolution.exists_mem_grade_zero_augmentation_eq`: a surjective augmentation
  killing the positive-degree part is already surjective from degree zero.
* `DividedPowers.TateResolution.bijective_cohomologyMap_regradedAugmentationHom`: the augmentation
  is a quasi-isomorphism, from the four elementary exactness conditions.

## Implementation notes

The cohomology of a differential graded algebra used by Situation 0BZB is
`DifferentialGradedAlgebra.Cohomology`, a quotient of the homogeneous cocycles, so the
bijectivity statement splits by degree. In positive cohomological degrees both sides vanish
because the regraded algebra has nothing there; in negative cohomological degree `-n` the source
vanishes by exactness in homological degree `n` and the target because `S` sits in degree zero;
in degree zero the surjectivity of the augmentation from degree zero gives surjectivity and
exactness at degree zero gives injectivity. The three degree-independent steps are isolated as
statements about an arbitrary differential graded algebra, so that nothing about the regrading
enters them.

The regraded algebra, the base ring and `S` are taken in a single universe, which is the encoding
of the differential graded chapter (Tag 09JJ) that `Dualizing.DGAResolution` inherits; the
statements below are therefore phrased for an algebra whose carrier lies in the universe of the
base ring, which is the case for a `DividedPowers.TateResolution.Resolution` whose variable set
does too.

## References

* [Stacks Project, Tag 0BZB](https://stacks.math.columbia.edu/tag/0BZB), the situation.
* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN), Tate resolutions.
* [Stacks Project, Tag 061V](https://stacks.math.columbia.edu/tag/061V), differential graded
  algebras.
-/

@[expose] public noncomputable section

universe u

/-! ### Degrees in which a differential graded algebra has no cohomology -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **A degree with no homogeneous elements carries no cohomology.** -/
theorem subsingleton_cohomology_of_grading_eq_bot (E : DifferentialGradedAlgebra.{u, u} R)
    {k : ℤ} (hk : E.grading k = ⊥) : Subsingleton (E.Cohomology k) := by
  constructor
  refine Quotient.ind₂ fun a b => ?_
  have ha : (a.1 : E.A) = 0 := (Submodule.eq_bot_iff _).mp hk _ a.1.2
  have hb : (b.1 : E.A) = 0 := (Submodule.eq_bot_iff _).mp hk _ b.1.2
  exact (Cohomology.mk_eq_mk_iff E k a b).mpr ⟨0, by simp [ha, hb]⟩

/-- **A degree in which every cocycle is a coboundary carries no cohomology.** -/
theorem subsingleton_cohomology_of_exact (E : DifferentialGradedAlgebra.{u, u} R) {k : ℤ}
    (h : ∀ a ∈ E.grading k, E.d a = 0 → ∃ c ∈ E.grading (k - 1), E.d c = a) :
    Subsingleton (E.Cohomology k) := by
  constructor
  refine Quotient.ind₂ fun a b => ?_
  obtain ⟨c, hc, hdc⟩ := h ((a.1 : E.A) - b.1) (Submodule.sub_mem _ a.1.2 b.1.2) (by
    rw [map_sub, show E.d (a.1 : E.A) = 0 from a.2, show E.d (b.1 : E.A) = 0 from b.2, sub_zero])
  exact (Cohomology.mk_eq_mk_iff E k a b).mpr ⟨⟨c, hc⟩, hdc.symm⟩

/-- A homomorphism between differential graded algebras without cohomology in a given degree is
bijective on cohomology in that degree. -/
theorem Hom.bijective_cohomologyMap_of_subsingleton
    {E F : DifferentialGradedAlgebra.{u, u} R} (φ : E.Hom F) (k : ℤ)
    (hE : Subsingleton (E.Cohomology k)) (hF : Subsingleton (F.Cohomology k)) :
    Function.Bijective (φ.cohomologyMap k) :=
  ⟨fun x y _ => hE.allEq x y,
    fun _ => ⟨Quotient.mk _ ⟨0, by simp⟩, hF.allEq _ _⟩⟩

end DifferentialGradedAlgebra

/-! ### Cohomology of an algebra concentrated in degree zero -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

/-- In an algebra concentrated in degree zero the differential vanishes, so a cohomology class
is determined by the underlying element. -/
theorem degreeZero_cocycle_eq_of_cohomology_mk_eq (k : ℤ)
    {a b : (degreeZero R S).Cocycle k}
    (h : (Quotient.mk _ a : (degreeZero R S).Cohomology k) = Quotient.mk _ b) :
    (a.1 : (degreeZero R S).A) = (b.1 : (degreeZero R S).A) := by
  obtain ⟨c, hc⟩ := (Cohomology.mk_eq_mk_iff (degreeZero R S) k a b).mp h
  have h0 : (degreeZero R S).d (c : (degreeZero R S).A) = 0 := rfl
  rw [h0] at hc
  exact sub_eq_zero.mp hc

/-- Two cocycles of an algebra concentrated in degree zero with the same underlying element have
the same cohomology class. -/
theorem degreeZero_cohomology_mk_eq_of_cocycle_eq (k : ℤ)
    {a b : (degreeZero R S).Cocycle k}
    (h : (a.1 : (degreeZero R S).A) = (b.1 : (degreeZero R S).A)) :
    (Quotient.mk _ a : (degreeZero R S).Cohomology k) = Quotient.mk _ b :=
  (Cohomology.mk_eq_mk_iff (degreeZero R S) k a b).mpr ⟨0, by simp [h]⟩

/-- **A homomorphism into an algebra concentrated in degree zero is bijective on degree-zero
cohomology** as soon as it is surjective from the degree-zero cocycles and its kernel there
consists of coboundaries. -/
theorem Hom.bijective_cohomologyMap_degreeZero {E : DifferentialGradedAlgebra.{u, u} R}
    (φ : E.Hom (degreeZero R S))
    (hsurj : ∀ s : S, ∃ a ∈ E.grading 0, E.d a = 0 ∧ φ.toAlgebraHom a = s)
    (hexact : ∀ a ∈ E.grading 0, φ.toAlgebraHom a = 0 →
      ∃ c ∈ E.grading (0 - 1), E.d c = a) :
    Function.Bijective (φ.cohomologyMap 0) := by
  constructor
  · refine Quotient.ind₂ fun a b hab => ?_
    rw [Hom.cohomologyMap_mk, Hom.cohomologyMap_mk] at hab
    have hval := degreeZero_cocycle_eq_of_cohomology_mk_eq 0 hab
    rw [Hom.cocycleMap_val, Hom.cocycleMap_val] at hval
    obtain ⟨c, hc, hdc⟩ := hexact ((a.1 : E.A) - b.1) (Submodule.sub_mem _ a.1.2 b.1.2) (by
      rw [map_sub, hval, sub_self])
    exact (Cohomology.mk_eq_mk_iff E 0 a b).mpr ⟨⟨c, hc⟩, hdc.symm⟩
  · refine Quotient.ind fun b => ?_
    obtain ⟨a, hamem, hda, ha⟩ := hsurj (b.1 : (degreeZero R S).A)
    refine ⟨Quotient.mk _ ⟨⟨a, hamem⟩, hda⟩, ?_⟩
    rw [Hom.cohomologyMap_mk]
    exact degreeZero_cohomology_mk_eq_of_cocycle_eq 0 (by rwa [Hom.cocycleMap_val])

end DifferentialGradedAlgebra

namespace DividedPowers.TateResolution

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {A : Type u} [Ring A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d] (ε : A →ₐ[R] S)

/-! ### The augmentation as a homomorphism of differential graded algebras -/

/-- **The augmentation of a nonnegatively graded resolution, read cohomologically.** An
augmentation that kills the positive-degree part and every boundary is a homomorphism of
differential graded algebras from the regraded algebra to `S` placed in degree zero with zero
differential. -/
def regradedAugmentationHom
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hd : ∀ a : A, ε (d a) = 0) :
    (regradedDifferentialGradedAlgebra 𝒜 d).Hom
      (DifferentialGradedAlgebra.degreeZero R S) where
  toAlgebraHom := ε
  map_grading n a ha := by
    have ha' : a ∈ cohomologicalGrade 𝒜 n := ha
    change ε a ∈ DifferentialGradedAlgebra.degreeZeroGrading R S n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [DifferentialGradedAlgebra.degreeZeroGrading_zero]
      exact Submodule.mem_top
    · rw [DifferentialGradedAlgebra.degreeZeroGrading_eq_bot R S hn, Submodule.mem_bot]
      rcases lt_or_ge 0 n with hn0 | hn0
      · rw [eq_zero_of_mem_cohomologicalGrade_of_pos 𝒜 hn0 ha', map_zero]
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
        rw [cohomologicalGrade_neg_natCast] at ha'
        exact hpos k a (by omega) ha'
  map_d a := (hd a).trans rfl

/-! ### The augmentation is a quasi-isomorphism -/

/-- **A surjective augmentation is surjective from degree zero.** If the augmentation kills the
positive-degree part then every element of `S` is already the image of a homogeneous element of
degree zero: the positive-degree components of a preimage do not contribute. -/
theorem exists_mem_grade_zero_augmentation_eq
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hsurj : Function.Surjective ε) (s : S) : ∃ a ∈ 𝒜 0, ε a = s := by
  classical
  obtain ⟨x, rfl⟩ := hsurj s
  refine ⟨((DirectSum.decompose 𝒜 x 0 : 𝒜 0) : A), (DirectSum.decompose 𝒜 x 0).2, ?_⟩
  have hx : (∑ i ∈ (DirectSum.decompose 𝒜 x).support,
      ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A)) = x :=
    DirectSum.sum_support_decompose 𝒜 x
  have hsum : (∑ i ∈ (DirectSum.decompose 𝒜 x).support,
      ε ((DirectSum.decompose 𝒜 x i : 𝒜 i) : A)) = ε x := by
    rw [← map_sum, hx]
  rw [← hsum]
  symm
  refine Finset.sum_eq_single 0 (fun i _ hi => ?_) (fun h0 => ?_)
  · exact hpos i _ (by omega) (DirectSum.decompose 𝒜 x i).2
  · simp [DFinsupp.notMem_support_iff.mp h0]

/-- A step of exactness in homological degree `n` is a step of exactness in cohomological degree
`-n`. -/
private theorem exists_mem_cohomologicalGrade_pred (𝒜 : ℕ → Submodule R A) (d : A →ₗ[R] A)
    {P : A → Prop} (n : ℕ)
    (h : ∀ a ∈ 𝒜 n, P a → ∃ b ∈ 𝒜 (n + 1), d b = a) {a : A}
    (ha : a ∈ cohomologicalGrade 𝒜 (-(n : ℤ))) (hP : P a) :
    ∃ c ∈ cohomologicalGrade 𝒜 (-(n : ℤ) - 1), d c = a := by
  rw [cohomologicalGrade_neg_natCast] at ha
  obtain ⟨c, hc, hdc⟩ := h a ha hP
  refine ⟨c, ?_, hdc⟩
  rwa [show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by push_cast; ring, cohomologicalGrade_neg_natCast]

/-- **The augmentation of a nonnegatively graded resolution is a quasi-isomorphism.** The four
elementary exactness conditions of a Tate resolution — the augmentation kills the positive-degree
part and every boundary, it is surjective, a degree-zero element it kills is a boundary from
degree one, and the complex is exact in every positive degree — say exactly that the regraded
augmentation is bijective on cohomology in every degree. -/
theorem bijective_cohomologyMap_regradedAugmentationHom
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hd : ∀ a : A, ε (d a) = 0)
    (hsurj : Function.Surjective ε)
    (hzero : ∀ a ∈ 𝒜 0, ε a = 0 → ∃ b ∈ 𝒜 1, d b = a)
    (hexact : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → d a = 0 → ∃ b ∈ 𝒜 (n + 1), d b = a)
    (k : ℤ) :
    Function.Bijective ((regradedAugmentationHom 𝒜 d ε hpos hd).cohomologyMap k) := by
  rcases eq_or_ne k 0 with rfl | hk
  · refine DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_degreeZero _ ?_ ?_
    · intro s
      obtain ⟨a, hamem, ha⟩ := exists_mem_grade_zero_augmentation_eq 𝒜 ε hpos hsurj s
      refine ⟨a, ?_, ?_, ha⟩
      · show a ∈ cohomologicalGrade 𝒜 0
        rwa [cohomologicalGrade_zero]
      · exact IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := 𝒜) (d := d) hamem
    · intro a ha hεa
      exact exists_mem_cohomologicalGrade_pred 𝒜 d (P := fun a => ε a = 0) 0
        (fun a ha h => hzero a ha h) (a := a) ha hεa
  · refine DifferentialGradedAlgebra.Hom.bijective_cohomologyMap_of_subsingleton _ k ?_ ?_
    · rcases lt_or_ge 0 k with hk0 | hk0
      · exact DifferentialGradedAlgebra.subsingleton_cohomology_of_grading_eq_bot _
          (cohomologicalGrade_of_pos 𝒜 hk0)
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨(-k).toNat, by omega⟩
        exact DifferentialGradedAlgebra.subsingleton_cohomology_of_exact _ fun a ha hda =>
          exists_mem_cohomologicalGrade_pred 𝒜 d (P := fun a => d a = 0) n
            (fun a ha h => hexact n a (by omega) ha h) ha hda
    · exact DifferentialGradedAlgebra.subsingleton_cohomology_of_grading_eq_bot _
        (DifferentialGradedAlgebra.degreeZeroGrading_eq_bot R S hk)

/-! ### Situation 0BZB from a nonnegatively graded resolution -/

/-- **Situation 0BZB from a nonnegatively graded resolution.** A nonnegatively graded algebra
with a differential lowering degrees by one, together with an augmentation to `S` satisfying the
four elementary exactness conditions of a Tate resolution, is a differential graded resolution of
`S` in the sense of Situation 0BZB: read cohomologically it is a differential graded `R`-algebra,
and its augmentation is a quasi-isomorphism onto `S` placed in degree zero. -/
def dgaResolutionOfAugmentation
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hd : ∀ a : A, ε (d a) = 0)
    (hsurj : Function.Surjective ε)
    (hzero : ∀ a ∈ 𝒜 0, ε a = 0 → ∃ b ∈ 𝒜 1, d b = a)
    (hexact : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → d a = 0 → ∃ b ∈ 𝒜 (n + 1), d b = a) :
    Dualizing.DGAResolution R S where
  E := regradedDifferentialGradedAlgebra 𝒜 d
  toTarget := regradedAugmentationHom 𝒜 d ε hpos hd
  quasiIso := bijective_cohomologyMap_regradedAugmentationHom 𝒜 d ε hpos hd hsurj hzero hexact

/-- The differential graded algebra of the resolution built from an augmentation is the
nonnegatively graded algebra read cohomologically. -/
theorem dgaResolutionOfAugmentation_E
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hd : ∀ a : A, ε (d a) = 0)
    (hsurj : Function.Surjective ε)
    (hzero : ∀ a ∈ 𝒜 0, ε a = 0 → ∃ b ∈ 𝒜 1, d b = a)
    (hexact : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → d a = 0 → ∃ b ∈ 𝒜 (n + 1), d b = a) :
    (dgaResolutionOfAugmentation 𝒜 d ε hpos hd hsurj hzero hexact).E =
      regradedDifferentialGradedAlgebra 𝒜 d := rfl

/-! ### A bundled Tate resolution as Situation 0BZB data -/

namespace Resolution

section General

variable {σ : Type u} {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ)

/-- **A Tate resolution, read cohomologically.** The carrier of a Tate resolution with its
grading placed in nonpositive cohomological degrees, as a differential graded `R`-algebra. -/
def regradedAlgebra : DifferentialGradedAlgebra.{u, u} R :=
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  regradedDifferentialGradedAlgebra T.grade T.differential

/-- **A Tate resolution is a differential graded resolution.** The data of Situation 0BZB
attached to a Tate resolution of `S`: its carrier read cohomologically, together with its
augmentation, which the resolution's exactness conditions make a quasi-isomorphism. -/
def toDGAResolution : Dualizing.DGAResolution R S :=
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  dgaResolutionOfAugmentation T.grade T.differential T.augmentation
    (fun n a hn ha => T.augmentation_positive n a hn ha)
    (fun a => T.augmentation_differential a)
    T.augmentation_surjective
    (fun a ha hεa => T.exact_zero a ha hεa)
    (fun n a hn ha hda => T.exact_positive n a hn ha hda)

/-- The differential graded algebra of the resolution attached to a Tate resolution is its
carrier read cohomologically. -/
theorem toDGAResolution_E : T.toDGAResolution.E = T.regradedAlgebra := rfl

end General

section Finite

variable {k : ℕ} {φ : MvPolynomial (Fin k) R →ₐ[R] S} (T : Resolution R S (Fin k) φ)

/-- **A Tate resolution along a presentation by finitely many variables is a differential graded
resolution.** This is the shape in which
`DividedPowers.TateResolution.exists_finite_tateResolution_of_pseudoCoherent` (Stacks 0BZ9)
produces a Tate resolution, so that its output is Situation 0BZB data. -/
def toDGAResolutionFin : Dualizing.DGAResolution R S :=
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  dgaResolutionOfAugmentation T.grade T.differential T.augmentation
    (fun n a hn ha => T.augmentation_positive n a hn ha)
    (fun a => T.augmentation_differential a)
    T.augmentation_surjective
    (fun a ha hεa => T.exact_zero a ha hεa)
    (fun n a hn ha hda => T.exact_positive n a hn ha hda)

end Finite

end Resolution

end DividedPowers.TateResolution

end
