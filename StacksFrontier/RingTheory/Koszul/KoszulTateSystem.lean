module

public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCategory
public import StacksFrontier.Algebra.Homology.DoubleQuasiIso
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateProSystemProregular
public import StacksFrontier.RingTheory.Dualizing.TateDifferentialGradedResolution
public import StacksFrontier.RingTheory.Koszul.PowSheafAlgebra
public import StacksFrontier.RingTheory.Koszul.WeaklyProregular

/-! # The Koszul--Tate ladder as inverse systems of differential graded algebras

Let `f₁, …, f_r` be a weakly proregular sequence in a ring `R`. The weakly proregular form of
Tag 0GZ5, `DividedPowers.TateResolution.exists_koszulTateProIso_of_isWeaklyProregular`, produces
exponents `1 = n₀ < n₁ < ⋯` and factorizations `K_{nᵢ₊₁} → Aᵢ → K_{nᵢ}` of the Koszul transition
maps through divided power differential graded resolutions `Aᵢ` of `R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})`,
all stated elementwise on homologically graded algebras. This file reads that ladder in the
bundled language of Chapter 22: each `Aᵢ` becomes an object of `DifferentialGradedAlgebra R`
(homological degree `k` in cohomological degree `-k`), the maps of the ladder become morphisms
of that category, the Tate algebras form an inverse system indexed by `ℕᵒᵖ`, and the maps
`K_{nᵢ₊₁} → Aᵢ`, `Aᵢ₊₁ → K_{nᵢ₊₁}` and `Aᵢ → R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁})` become natural
transformations, the last a quasi-isomorphism in every stage, while the first two compose in
either order to the transition maps, so that they are mutually inverse pro-morphisms.

## Main definitions

* `DifferentialGradedAlgebra.regularModuleDegreeZeroIso`: the complex underlying an algebra
  concentrated in degree zero is that algebra placed in degree zero.
* `Koszul.powAugmentationHom`: the Koszul augmentation `K_N → R/(f₁^N, …, f_r^N)` as a
  homomorphism of differential graded algebras.
* `DividedPowers.TateResolution.KoszulTateFactorization.toDGA`, `.upHom`, `.downHom`, `.augHom`
  and `.proTransitionHom`: one factorization, and the transition between two consecutive ones,
  in the category of differential graded algebras.
* `Koszul.powAlgebraSeq` and `Koszul.powQuotientSeq`: the Koszul system and the quotient system
  along a monotone sequence of exponents.
* `DividedPowers.TateResolution.koszulTateDGASystem`: the Tate system `(Aᵢ)ᵢ`.
* `DividedPowers.TateResolution.koszulTateUp`, `DividedPowers.TateResolution.koszulTateDown` and
  `DividedPowers.TateResolution.koszulTateAug`: the maps of inverse systems
  `(K_{nᵢ₊₁}) → (Aᵢ)`, `(Aᵢ₊₁) → (K_{nᵢ₊₁})` and `(Aᵢ) → (R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁}))`.

## Main results

* `DividedPowers.TateResolution.quasiIso_toCochainMap_regradedAugmentationHom`: the augmentation
  of a nonnegatively graded resolution is a quasi-isomorphism of the underlying complexes.
* `Koszul.powAugmentationHom_toCochainMap`: the cochain map of `Koszul.powAugmentationHom` is the
  Koszul augmentation `Koszul.powAugmentation`.
* `DividedPowers.TateResolution.KoszulTateFactorization.upHom_downHom`,
  `.upHom_augHom`, `.proTransitionHom_downHom`, `.upHom_proTransitionHom` and
  `.proTransitionHom_augHom`: the ladder commutes in the category of differential graded algebras.
* `DividedPowers.TateResolution.KoszulTateFactorization.quasiIso_augHom` and
  `DividedPowers.TateResolution.quasiIso_koszulTateAug_app`: each Tate algebra resolves its
  quotient.
* `DividedPowers.TateResolution.koszulTateDown_app_koszulTateUp_app` and
  `DividedPowers.TateResolution.koszulTateUp_app_koszulTateDown_app`: the two maps between the
  Koszul and the Tate systems compose to the transition maps.

## References

* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
* [Stacks Project, Tag 0GZ5](https://stacks.math.columbia.edu/tag/0GZ5)
* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u

/-! ### Cochain complexes of algebras concentrated in degree zero -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- A degree with no homogeneous elements contributes a zero object to the underlying cochain
complex of a differential graded algebra. -/
theorem isZero_regularModule_toCochainComplex_X (E : DifferentialGradedAlgebra.{u, u} R)
    {n : ℤ} (h : E.grading n = ⊥) :
    Limits.IsZero ((regularModule E).toCochainComplex.X n) := by
  have : Subsingleton (E.grading n) := by
    rw [h]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (E.grading n))

/-- **Exactness of the underlying complex from cycles and boundaries.** If every cocycle of
degree `m + 1` is the differential of an element of degree `m`, the underlying cochain complex is
exact in degree `m + 1`. -/
theorem exactAt_regularModule_toCochainComplex (E : DifferentialGradedAlgebra.{u, u} R) (m : ℤ)
    (h : ∀ a ∈ E.grading (m + 1), E.d a = 0 → ∃ b ∈ E.grading m, E.d b = a) :
    (regularModule E).toCochainComplex.ExactAt (m + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro (x : E.grading (m + 1)) hx
  have hx' : E.d (x : E.A) = 0 := by
    have h' := congrArg Subtype.val hx
    simp only [HomologicalComplex.shortComplexFunctor'_obj_g, toCochainComplex_d] at h'
    exact h'
  obtain ⟨b, hb, hdb⟩ := h x x.2 hx'
  refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
  simp only [HomologicalComplex.shortComplexFunctor'_obj_f, toCochainComplex_d]
  exact hdb

variable (R) (S : Type u) [Ring S] [Algebra R S]

/-- The inclusion of the degree-zero piece of an algebra concentrated in degree zero. -/
def degreeZeroGradingSubtype :
    (regularModule (degreeZero R S)).toCochainComplex.X 0 ⟶ ModuleCat.of R S :=
  ModuleCat.ofHom (degreeZeroGrading R S 0).subtype

/-- The whole algebra, as its degree-zero piece. -/
def toDegreeZeroGrading :
    ModuleCat.of R S ⟶ (regularModule (degreeZero R S)).toCochainComplex.X 0 :=
  ModuleCat.ofHom (LinearMap.codRestrict (degreeZeroGrading R S 0) LinearMap.id fun x => by
    rw [degreeZeroGrading_zero]
    exact Submodule.mem_top)

/-- Viewing the algebra as its degree-zero piece and including back is the identity. -/
theorem toDegreeZeroGrading_degreeZeroGradingSubtype :
    toDegreeZeroGrading R S ≫ degreeZeroGradingSubtype R S = 𝟙 _ := by
  ext x
  rfl

/-- Including the degree-zero piece and viewing the algebra as it again is the identity. -/
theorem degreeZeroGradingSubtype_toDegreeZeroGrading :
    degreeZeroGradingSubtype R S ≫ toDegreeZeroGrading R S = 𝟙 _ := by
  ext x
  rfl

/-- **The underlying complex of an algebra concentrated in degree zero is the algebra placed in
degree zero.** -/
def regularModuleDegreeZeroIso :
    (regularModule (degreeZero R S)).toCochainComplex ≅
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R S) where
  hom := HomologicalComplex.mkHomToSingle (degreeZeroGradingSubtype R S) fun i hi =>
    (isZero_regularModule_toCochainComplex_X _ (degreeZeroGrading_eq_bot R S
      (show i ≠ 0 by have h : i + 1 = 0 := hi; omega))).eq_of_src _ _
  inv := HomologicalComplex.mkHomFromSingle (toDegreeZeroGrading R S) fun k hk =>
    (isZero_regularModule_toCochainComplex_X _ (degreeZeroGrading_eq_bot R S
      (show k ≠ 0 by have h : 0 + 1 = k := hk; omega))).eq_of_tgt _ _
  hom_inv_id := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    by_cases hn : n = 0
    · subst hn
      rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
        HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc,
        degreeZeroGradingSubtype_toDegreeZeroGrading, HomologicalComplex.id_f]
    · exact (isZero_regularModule_toCochainComplex_X _
        (degreeZeroGrading_eq_bot R S hn)).eq_of_src _ _
  inv_hom_id := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f,
      HomologicalComplex.mkHomFromSingle_f, Category.assoc,
      reassoc_of% toDegreeZeroGrading_degreeZeroGradingSubtype R S, Iso.hom_inv_id,
      HomologicalComplex.id_f]

/-- In degree zero the identification `regularModuleDegreeZeroIso` is the inclusion of
the degree-zero piece, followed by the identification of the single complex in degree zero. -/
theorem regularModuleDegreeZeroIso_hom_f_zero :
    (regularModuleDegreeZeroIso R S).hom.f 0 = degreeZeroGradingSubtype R S ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R S)).inv := by
  dsimp only [regularModuleDegreeZeroIso]
  exact HomologicalComplex.mkHomToSingle_f _ _

end DifferentialGradedAlgebra

namespace DividedPowers.TateResolution

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

section Regraded

variable {A B : Type u} [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-- An algebra homomorphism preserving the homological degrees preserves the cohomological
ones. -/
theorem map_mem_cohomologicalGrade {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R B}
    (φ : A →ₐ[R] B) (h : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → φ a ∈ ℬ k) {n : ℤ} {a : A}
    (ha : a ∈ cohomologicalGrade 𝒜 n) : φ a ∈ cohomologicalGrade ℬ n := by
  rcases le_or_gt n 0 with hn | hn
  · rw [cohomologicalGrade_of_nonpos _ hn] at ha ⊢
    exact h _ a ha
  · rw [eq_zero_of_mem_cohomologicalGrade_of_pos _ hn ha, map_zero]
    exact Submodule.zero_mem _

variable {S : Type u} [CommRing S] [Algebra R S] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (d : A →ₗ[R] A) [IsDifferentialGradedAlgebra 𝒜 d] (ε : A →ₐ[R] S)

/-- **The augmentation of a nonnegatively graded resolution is a quasi-isomorphism of cochain
complexes.** Under the four elementary exactness conditions of a Tate resolution, the map of
underlying cochain complexes of `DividedPowers.TateResolution.regradedAugmentationHom` is a
quasi-isomorphism: in positive degrees both complexes vanish, in negative degrees the target
vanishes and the source is exact, and in degree zero the augmentation is surjective from the
degree-zero piece with the boundaries as kernel. -/
theorem quasiIso_toCochainMap_regradedAugmentationHom
    (hpos : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → ε a = 0)
    (hd : ∀ a : A, ε (d a) = 0)
    (hsurj : Function.Surjective ε)
    (hzero : ∀ a ∈ 𝒜 0, ε a = 0 → ∃ b ∈ 𝒜 1, d b = a)
    (hexact : ∀ (n : ℕ) (a : A), 0 < n → a ∈ 𝒜 n → d a = 0 → ∃ b ∈ 𝒜 (n + 1), d b = a) :
    QuasiIso (regradedAugmentationHom 𝒜 d ε hpos hd).toCochainMap := by
  have hL : ∀ n : ℤ, n ≠ 0 → Limits.IsZero
      ((regularModule (degreeZero R S)).toCochainComplex.X n) := fun n hn =>
    isZero_regularModule_toCochainComplex_X _ (degreeZeroGrading_eq_bot R S hn)
  have hK : ∀ n : ℤ, 0 < n → Limits.IsZero
      ((regularModule (regradedDifferentialGradedAlgebra 𝒜 d)).toCochainComplex.X n) :=
    fun n hn => isZero_regularModule_toCochainComplex_X _ (cohomologicalGrade_of_pos 𝒜 hn)
  have hgr : ∀ (k : ℕ) (a : A),
      a ∈ (regularModule (regradedDifferentialGradedAlgebra 𝒜 d)).grading (-(k : ℤ)) ↔
        a ∈ 𝒜 k := fun k a => by
    change a ∈ cohomologicalGrade 𝒜 _ ↔ _
    rw [cohomologicalGrade_neg_natCast]
  rw [quasiIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [quasiIsoAt_iff_exactAt' _ _ (HomologicalComplex.exactAt_of_isZero_X _ _ (hL n hn.ne))]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k + 2 : ℕ) : ℤ) + 1 := ⟨(-n).toNat - 1, by omega⟩
    refine exactAt_regularModule_toCochainComplex _ _ fun a ha hda => ?_
    rw [show -((k + 2 : ℕ) : ℤ) + 1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at ha
    obtain ⟨b, hb, hdb⟩ := hexact (k + 1) a (by omega) ((hgr _ a).1 ha) hda
    exact ⟨b, (hgr _ b).2 hb, hdb⟩
  · rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    refine (ShortComplex.quasiIso_iff_of_zeros' _ ((hK 1 one_pos).eq_of_tgt _ _)
      ((hL (-1) (by norm_num)).eq_of_src _ _) ((hL 1 one_ne_zero).eq_of_tgt _ _)).2 ⟨?_, ?_⟩
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (x : cohomologicalGrade 𝒜 0) hx
      have hεx : ε (x : A) = 0 := congrArg Subtype.val hx
      obtain ⟨b, hb, hdb⟩ := hzero x ((hgr 0 x).1 x.2) hεx
      refine ⟨⟨b, (hgr 1 b).2 hb⟩, Subtype.ext ?_⟩
      have hd' : (regularModule (regradedDifferentialGradedAlgebra 𝒜 d)).toCochainComplex.d
          (-1) 0 = ModuleCat.ofHom
            ((regularModule (regradedDifferentialGradedAlgebra 𝒜 d)).gradedDifferential (-1)) :=
        toCochainComplex_d _ (-1)
      simp only [HomologicalComplex.shortComplexFunctor'_obj_f]
      rwa [hd']
    · refine (ModuleCat.epi_iff_surjective _).2 fun (y : degreeZeroGrading R S 0) => ?_
      obtain ⟨a, ha, hεa⟩ := exists_mem_grade_zero_augmentation_eq 𝒜 ε hpos hsurj (y : S)
      exact ⟨⟨a, (hgr 0 a).2 ha⟩, Subtype.ext hεa⟩
  · exact HomologicalComplex.quasiIsoAt_of_isZero_X _ n (hK n hn) (hL n hn.ne')

end Regraded

/-! ### The Koszul augmentation as a homomorphism of differential graded algebras -/

section KoszulAugmentation

open scoped ExteriorAlgebra

variable {r : ℕ}

/-- The canonical map onto `R/(f₁^N, …, f_r^N)` kills every exterior power of positive
degree. -/
theorem koszulPowerAugmentation_eq_zero_of_mem (f : Fin r → R) (N : ℕ) {k : ℕ} (hk : 0 < k)
    {x : ExteriorAlgebra R (Fin r → R)} (hx : x ∈ exteriorGrade R (Fin r → R) k) :
    koszulPowerAugmentation f N x = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hle : exteriorGrade R (Fin r → R) (j + 1) ≤
      LinearMap.ker (koszulPowerAugmentation f N).toLinearMap := by
    change LinearMap.range (ExteriorAlgebra.ι R) ^ (j + 1) ≤ _
    rw [pow_succ']
    refine Submodule.mul_le.2 fun a ha b _ => ?_
    obtain ⟨p, rfl⟩ := ha
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_mul, koszulPowerAugmentation_ι,
      zero_mul]
  exact hle hx

/-- The canonical map onto `R/(f₁^N, …, f_r^N)` kills the boundaries of the Koszul algebra. -/
theorem koszulPowerAugmentation_koszulPowerDifferential (f : Fin r → R) (N : ℕ)
    (x : ExteriorAlgebra R (Fin r → R)) :
    koszulPowerAugmentation f N (koszulPowerDifferential f N x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [koszulPowerDifferential, Koszul.contraction, CliffordAlgebra.contractLeft_algebraMap,
      map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul x p hx =>
    rw [koszulPowerDifferential, Koszul.contraction, CliffordAlgebra.contractLeft_ι_mul,
      map_sub, map_smul, map_mul]
    change _ - koszulPowerAugmentation f N (ExteriorAlgebra.ι R p) * _ = 0
    rw [koszulPowerAugmentation_ι, zero_mul, sub_zero, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 (show _ ∈ koszulPowerIdeal f N from
        Koszul.seqDual_mem_powIdeal f N p), zero_mul]

end KoszulAugmentation

end DividedPowers.TateResolution

namespace Koszul

open DividedPowers.TateResolution DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

/- The Koszul algebra is reached through the projections of a structure literal, and the ideal of
the `N`-th powers has two spellings, `Koszul.powIdeal` and
`DividedPowers.TateResolution.koszulPowerIdeal`, equal by definition; instance search must be
allowed to unfold all of them. -/
attribute [local implicit_reducible] powAlgebra cohomologicalDifferentialGradedAlgebra
  powIdeal koszulPowerIdeal

/-- **The Koszul augmentation `K_N → R/(f₁^N, …, f_r^N)` as a homomorphism of differential
graded algebras**, the target concentrated in degree zero. -/
def powAugmentationHom (f : Fin r → R) (N : ℕ) :
    powAlgebra f N ⟶ degreeZero R (R ⧸ powIdeal f N) :=
  DifferentialGradedAlgebra.Hom.mk (koszulPowerAugmentation f N)
    (fun n x hx => by
      change koszulPowerAugmentation f N x ∈ degreeZeroGrading R _ n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [degreeZeroGrading_zero]
        exact Submodule.mem_top
      · rw [degreeZeroGrading_eq_bot R _ hn, Submodule.mem_bot]
        change x ∈ cohomologicalGrade (exteriorGrade R (Fin r → R)) n at hx
        rcases lt_or_gt_of_ne hn with hn0 | hn0
        · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
          rw [cohomologicalGrade_neg_natCast] at hx
          exact koszulPowerAugmentation_eq_zero_of_mem f N (by omega) hx
        · rw [eq_zero_of_mem_cohomologicalGrade_of_pos _ hn0 hx, map_zero])
    (fun x => koszulPowerAugmentation_koszulPowerDifferential f N x)

/-- The underlying algebra homomorphism of `Koszul.powAugmentationHom` is the canonical map
`DividedPowers.TateResolution.koszulPowerAugmentation`. -/
@[simp]
theorem powAugmentationHom_toAlgebraHom (f : Fin r → R) (N : ℕ) :
    (powAugmentationHom f N).toAlgebraHom = koszulPowerAugmentation f N :=
  rfl

/-- **The cochain map underlying `Koszul.powAugmentationHom` is the Koszul augmentation**
`Koszul.powAugmentation`, once the complex underlying `R/(f₁^N, …, f_r^N)` concentrated in degree
zero is identified with the quotient placed in degree zero. -/
theorem powAugmentationHom_toCochainMap (f : Fin r → R) (N : ℕ) :
    (powAugmentationHom f N).toCochainMap ≫
        (regularModuleDegreeZeroIso R (R ⧸ powIdeal f N)).hom =
      powAugmentation f N := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, regularModuleDegreeZeroIso_hom_f_zero, powAugmentation_f_zero,
    ← Category.assoc]
  congr 1
  ext x
  exact (congrArg (koszulPowerAugmentation f N) (coe_eq_algebraMap_gradeZeroEquiv f N x)).trans
    (koszulPowerAugmentation_algebraMap f N _)

/-- **The Koszul augmentation is an isomorphism on cohomology in degree zero**, read on
`Koszul.powAugmentationHom`. -/
theorem quasiIsoAt_powAugmentationHom_toCochainMap (f : Fin r → R) (N : ℕ) :
    QuasiIsoAt (powAugmentationHom f N).toCochainMap 0 := by
  have h := quasiIsoAt_powAugmentation f N
  rw [← powAugmentationHom_toCochainMap] at h
  exact (quasiIsoAt_iff_comp_right _ _ 0).1 h

end Koszul

/-! ### One factorization as differential graded algebras -/

namespace DividedPowers.TateResolution

namespace KoszulTateFactorization

open DifferentialGradedAlgebra

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local implicit_reducible] Koszul.powAlgebra
  Koszul.cohomologicalDifferentialGradedAlgebra Koszul.powIdeal koszulPowerIdeal

variable {R : Type u} [CommRing R] {r : ℕ} {f : Fin r → R} {n m m' : ℕ}

/-- **The Tate algebra of a factorization, read cohomologically**: its divided power graded
algebra with the homological degree `k` in cohomological degree `-k`, as an object of
`DifferentialGradedAlgebra`. -/
def toDGA (s : KoszulTateFactorization f n) : DifferentialGradedAlgebra.{u, u} R :=
  haveI := s.dga
  regradedDifferentialGradedAlgebra s.A.grade s.d

/-- The map `K_N → A` of a factorization, as a homomorphism of differential graded algebras. -/
def upHom (s : KoszulTateFactorization f n) : Koszul.powAlgebra f s.topPower ⟶ s.toDGA :=
  Hom.mk s.up (fun _ _ hx => map_mem_cohomologicalGrade (𝒜 := exteriorGrade R (Fin r → R))
    s.up s.up_grade hx) s.up_d

/-- The map `A → K_n` of a factorization, as a homomorphism of differential graded algebras. -/
def downHom (s : KoszulTateFactorization f n) : s.toDGA ⟶ Koszul.powAlgebra f n :=
  Hom.mk s.down (fun _ _ ha => map_mem_cohomologicalGrade (ℬ := exteriorGrade R (Fin r → R))
    s.down s.down_grade ha) s.down_d

/-- The augmentation `A → R/(f₁^N, …, f_r^N)` of a factorization, as a homomorphism of
differential graded algebras, the target concentrated in degree zero. -/
def augHom (s : KoszulTateFactorization f n) :
    s.toDGA ⟶ degreeZero R (R ⧸ Koszul.powIdeal f s.topPower) :=
  haveI := s.dga
  regradedAugmentationHom s.A.grade s.d s.aug s.aug_positive s.aug_d

/-- The underlying algebra homomorphism of `upHom` is the map `K_N → A`. -/
@[simp]
theorem upHom_toAlgebraHom (s : KoszulTateFactorization f n) : s.upHom.toAlgebraHom = s.up :=
  rfl

/-- The underlying algebra homomorphism of `downHom` is the map `A → K_n`. -/
@[simp]
theorem downHom_toAlgebraHom (s : KoszulTateFactorization f n) :
    s.downHom.toAlgebraHom = s.down :=
  rfl

/-- The underlying algebra homomorphism of `augHom` is the augmentation. -/
@[simp]
theorem augHom_toAlgebraHom (s : KoszulTateFactorization f n) :
    s.augHom.toAlgebraHom = s.aug :=
  rfl

/-- The composite `K_N → A → K_n` is the Koszul transition homomorphism. -/
theorem upHom_downHom (s : KoszulTateFactorization f n) (hn : 1 ≤ n) :
    s.upHom ≫ s.downHom = Koszul.powTransition f hn s.lt.le :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun x => s.down_up x)

/-- The composite `K_N → A → R/(f₁^N, …, f_r^N)` is the Koszul augmentation. -/
theorem upHom_augHom (s : KoszulTateFactorization f n) :
    s.upHom ≫ s.augHom = Koszul.powAugmentationHom f s.topPower :=
  hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun x => s.aug_up x)

/-- **The Tate algebra resolves the quotient**: the cochain map underlying the augmentation
`A → R/(f₁^N, …, f_r^N)` is a quasi-isomorphism. -/
theorem quasiIso_augHom (s : KoszulTateFactorization f n) :
    QuasiIso s.augHom.toCochainMap :=
  have := s.dga
  quasiIso_toCochainMap_regradedAugmentationHom s.A.grade s.d s.aug s.aug_positive s.aug_d
    s.aug_surjective s.exists_d_eq_of_aug_eq_zero fun k a hk ha hda => by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact s.exists_d_eq_of_cycle j a ha hda

/-- The map `A → K_n` induces the canonical map `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)`: the
identity of `down_homology`, extended from degree zero to the whole algebra, both sides vanishing
in positive degrees. -/
theorem koszulPowerAugmentation_down (s : KoszulTateFactorization f n) (a : s.A.carrier) :
    koszulPowerAugmentation f n (s.down a) =
      Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f s.lt.le) (s.aug a) := by
  induction a using DirectSum.Decomposition.inductionOn s.A.grade with
  | zero => simp
  | @homogeneous k a =>
    obtain ⟨a, ha⟩ := a
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact s.down_homology a ha
    · rw [koszulPowerAugmentation_eq_zero_of_mem f n hk (s.down_grade k a ha),
        s.aug_positive k a hk ha, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- **The transition homomorphism of the Tate system** between two consecutive factorizations,
the composite `A' → K → A` through the Koszul algebra resolved by the lower one. -/
def proTransitionHom (t : KoszulTateFactorization f m') (s : KoszulTateFactorization f m)
    (h : m' = s.topPower) : t.toDGA ⟶ s.toDGA :=
  Hom.mk (t.proTransition s) (fun _ _ ha => map_mem_cohomologicalGrade (t.proTransition s)
    (t.proTransition_grade s) ha) (t.proTransition_d s h)

/-- The underlying algebra homomorphism of `proTransitionHom` is `proTransition`. -/
@[simp]
theorem proTransitionHom_toAlgebraHom (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) :
    (t.proTransitionHom s h).toAlgebraHom = t.proTransition s :=
  rfl

/-- The transition homomorphism of the Tate system is `A' → K_{m'} = K_N → A`. -/
theorem proTransitionHom_eq (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) :
    t.proTransitionHom s h =
      t.downHom ≫ eqToHom (congrArg (Koszul.powAlgebra f) h) ≫ s.upHom := by
  subst h
  exact hom_eq_of_toAlgebraHom_eq rfl

/-- **The lower square of the ladder**: `A' → A → K_m` is `A' → K_{m'} → K_m`. -/
theorem proTransitionHom_downHom (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) (hm : 1 ≤ m) :
    t.proTransitionHom s h ≫ s.downHom =
      t.downHom ≫ Koszul.powTransition f hm (s.lt.le.trans h.symm.le) := by
  subst h
  exact hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun a => s.down_up (t.down a))

/-- **The upper square of the ladder**: `K_{N'} → A' → A` is `K_{N'} → K_N → A`. -/
theorem upHom_proTransitionHom (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) :
    t.upHom ≫ t.proTransitionHom s h =
      Koszul.powTransition f (Nat.one_le_of_lt s.lt) (h.symm.le.trans t.lt.le) ≫ s.upHom := by
  subst h
  exact hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun x => congrArg s.up (t.down_up x))

/-- The transition homomorphism of the Tate system is compatible with the augmentations: the
square formed with `R/(f₁^{N'}, …, f_r^{N'}) → R/(f₁^N, …, f_r^N)` commutes. -/
theorem proTransitionHom_augHom (t : KoszulTateFactorization f m')
    (s : KoszulTateFactorization f m) (h : m' = s.topPower) :
    t.proTransitionHom s h ≫ s.augHom = t.augHom ≫ degreeZeroHom
      (Ideal.Quotient.factorₐ R (Koszul.powIdeal_le f (h.symm.le.trans t.lt.le))) := by
  subst h
  refine hom_eq_of_toAlgebraHom_eq (AlgHom.ext fun a => ?_)
  change s.aug (s.up (t.down a)) =
    Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f t.lt.le) (t.aug a)
  rw [s.aug_up]
  exact t.koszulPowerAugmentation_down a

end KoszulTateFactorization

end DividedPowers.TateResolution

/-! ### The two inverse systems -/

namespace Koszul

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The Koszul algebras on the powers of `f` along a monotone sequence of exponents `e`, all at
least `1`, as an inverse system indexed by `ℕᵒᵖ`: the stage `i` is `K_{e i}` and the transition
maps are the Koszul transition homomorphisms. For `e i = i + 1` this is
`Koszul.powAlgebraDiagram`. -/
def powAlgebraSeq (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) (h1 : ∀ i, 1 ≤ e i) :
    ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R where
  obj i := powAlgebra f (e i.unop)
  map {_ j} g := powTransition f (h1 j.unop) (he (leOfHom g.unop))
  map_id _ := hom_eq_of_toAlgebraHom_eq (powTransition_self_toAlgebraHom f _)
  map_comp {_ _ _} _ _ := hom_eq_of_toAlgebraHom_eq (powTransition_comp f _ _ _).symm

/-- The stage `i` of `Koszul.powAlgebraSeq` is `K_{e i}`. -/
@[simp]
theorem powAlgebraSeq_obj (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) (h1 : ∀ i, 1 ≤ e i)
    (i : ℕᵒᵖ) : (powAlgebraSeq f e he h1).obj i = powAlgebra f (e i.unop) :=
  rfl

/-- The transition maps of `Koszul.powAlgebraSeq` are the Koszul transition homomorphisms. -/
@[simp]
theorem powAlgebraSeq_map (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) (h1 : ∀ i, 1 ≤ e i)
    {i j : ℕᵒᵖ} (g : i ⟶ j) :
    (powAlgebraSeq f e he h1).map g = powTransition f (h1 j.unop) (he (leOfHom g.unop)) :=
  rfl

/-- Along the exponents `i + 1` the Koszul system is `Koszul.powAlgebraDiagram`. -/
theorem powAlgebraSeq_succ (f : Fin r → R) :
    powAlgebraSeq f (· + 1) (fun _ _ h => Nat.succ_le_succ h)
      (fun i => Nat.succ_le_succ (Nat.zero_le i)) = powAlgebraDiagram f :=
  rfl

/-- The quotients `R/(f₁^{e i}, …, f_r^{e i})` along a monotone sequence of exponents `e`,
concentrated in degree zero, as an inverse system indexed by `ℕᵒᵖ`. For `e i = i + 1` this is
`Koszul.powQuotientAlgebraDiagram`. -/
def powQuotientSeq (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) :
    ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R where
  obj i := degreeZero R (R ⧸ powIdeal f (e i.unop))
  map {_ _} g := degreeZeroHom (Ideal.Quotient.factorₐ R (powIdeal_le f (he (leOfHom g.unop))))
  map_id _ := hom_eq_of_toAlgebraHom_eq (by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)
  map_comp {_ _ _} _ _ := hom_eq_of_toAlgebraHom_eq (by
    refine AlgHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)

/-- The stage `i` of `Koszul.powQuotientSeq` is `R/(f₁^{e i}, …, f_r^{e i})` in degree zero. -/
@[simp]
theorem powQuotientSeq_obj (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) (i : ℕᵒᵖ) :
    (powQuotientSeq f e he).obj i = degreeZero R (R ⧸ powIdeal f (e i.unop)) :=
  rfl

/-- The transition maps of `Koszul.powQuotientSeq` are the canonical surjections. -/
@[simp]
theorem powQuotientSeq_map (f : Fin r → R) (e : ℕ → ℕ) (he : Monotone e) {i j : ℕᵒᵖ}
    (g : i ⟶ j) : (powQuotientSeq f e he).map g =
      degreeZeroHom (Ideal.Quotient.factorₐ R (powIdeal_le f (he (leOfHom g.unop)))) :=
  rfl

/-- Along the exponents `i + 1` the quotient system is `Koszul.powQuotientAlgebraDiagram`. -/
theorem powQuotientSeq_succ (f : Fin r → R) :
    powQuotientSeq f (· + 1) (fun _ _ h => Nat.succ_le_succ h) = powQuotientAlgebraDiagram f :=
  rfl

end Koszul

namespace DividedPowers.TateResolution

open DifferentialGradedAlgebra KoszulTateFactorization

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (proregular : Koszul.IsWeaklyProregular f)

/-- Every exponent of the Koszul--Tate ladder is at least `1`. -/
theorem one_le_koszulTateFactorizationPower (i : ℕ) :
    1 ≤ koszulTateFactorizationPower f proregular i :=
  (koszulTateFactorizationPower_zero f proregular).symm.le.trans
    ((strictMono_koszulTateFactorizationPower f proregular).monotone (Nat.zero_le i))

/-- The exponents `n₁ < n₂ < ⋯` resolved by the stages of the Koszul--Tate ladder are
monotone. -/
theorem monotone_koszulTateFactorizationPower_succ :
    Monotone fun i => koszulTateFactorizationPower f proregular (i + 1) :=
  fun _ _ h => (strictMono_koszulTateFactorizationPower f proregular).monotone
    (Nat.succ_le_succ h)

/-- **The Koszul system `(K_{nᵢ₊₁})ᵢ` of the Koszul--Tate ladder**: the Koszul algebras over the
exponents resolved by its stages. -/
abbrev koszulTateKoszulSystem : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  Koszul.powAlgebraSeq f (fun i => koszulTateFactorizationPower f proregular (i + 1))
    (monotone_koszulTateFactorizationPower_succ f proregular)
    (fun i => one_le_koszulTateFactorizationPower f proregular (i + 1))

/-- **The quotient system `(R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁}))ᵢ` of the Koszul--Tate ladder.** -/
abbrev koszulTateQuotientSystem : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  Koszul.powQuotientSeq f (fun i => koszulTateFactorizationPower f proregular (i + 1))
    (monotone_koszulTateFactorizationPower_succ f proregular)

/-- **The Tate system `(Aᵢ)ᵢ` of a weakly proregular sequence**, as an inverse system of
differential graded algebras indexed by `ℕᵒᵖ`: the stage `i` is the Tate algebra of the `i`-th
factorization of the Koszul--Tate ladder, and `Aᵢ₊₁ → Aᵢ` is the composite
`Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ`. -/
def koszulTateDGASystem : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  Functor.ofOpSequence (X := fun i => (koszulTateFactorizationStage f proregular i).toDGA)
    fun i => (koszulTateFactorizationStage f proregular (i + 1)).proTransitionHom
      (koszulTateFactorizationStage f proregular i)
      (koszulTateFactorizationStage_topPower f proregular i).symm

/-- The stage `i` of the Tate system is the Tate algebra of the `i`-th factorization. -/
@[simp]
theorem koszulTateDGASystem_obj (i : ℕᵒᵖ) :
    (koszulTateDGASystem f proregular).obj i =
      (koszulTateFactorizationStage f proregular i.unop).toDGA :=
  rfl

/-- The transition homomorphism `Aᵢ₊₁ → Aᵢ` of the Tate system. -/
theorem koszulTateDGASystem_map_succ (i : ℕ) (h : i ≤ i + 1) :
    (koszulTateDGASystem f proregular).map (homOfLE h).op =
      (koszulTateFactorizationStage f proregular (i + 1)).proTransitionHom
        (koszulTateFactorizationStage f proregular i)
        (koszulTateFactorizationStage_topPower f proregular i).symm :=
  Functor.ofOpSequence_map_homOfLE_succ _ i

/-- The Tate system shifted by one, `i ↦ Aᵢ₊₁`. -/
def koszulTateDGASystemShift : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  (Monotone.functor (f := fun i : ℕ => i + 1) fun _ _ h => Nat.succ_le_succ h).op ⋙
    koszulTateDGASystem f proregular

/-- The stage `i` of the shifted Tate system is the Tate algebra of the `(i+1)`-st
factorization. -/
@[simp]
theorem koszulTateDGASystemShift_obj (i : ℕᵒᵖ) :
    (koszulTateDGASystemShift f proregular).obj i =
      (koszulTateFactorizationStage f proregular (i.unop + 1)).toDGA :=
  rfl

/-- **The map `(K_{nᵢ₊₁})ᵢ → (Aᵢ)ᵢ` of inverse systems**, with components the maps
`K_{nᵢ₊₁} → Aᵢ` of the factorizations. -/
def koszulTateUp : koszulTateKoszulSystem f proregular ⟶ koszulTateDGASystem f proregular :=
  NatTrans.ofOpSequence (fun i => (koszulTateFactorizationStage f proregular i).upHom)
    fun i => by
      rw [koszulTateDGASystem_map_succ]
      exact (upHom_proTransitionHom _ _ _).symm

/-- The components of `koszulTateUp` are the maps `K_{nᵢ₊₁} → Aᵢ`. -/
@[simp]
theorem koszulTateUp_app (i : ℕᵒᵖ) :
    (koszulTateUp f proregular).app i = (koszulTateFactorizationStage f proregular i.unop).upHom :=
  rfl

/-- **The map `(Aᵢ₊₁)ᵢ → (K_{nᵢ₊₁})ᵢ` of inverse systems**, with components the maps
`Aᵢ₊₁ → K_{nᵢ₊₁}` of the factorizations. -/
def koszulTateDown :
    koszulTateDGASystemShift f proregular ⟶ koszulTateKoszulSystem f proregular :=
  NatTrans.ofOpSequence (fun i => (koszulTateFactorizationStage f proregular (i + 1)).downHom)
    fun i => by
      have h : (koszulTateDGASystemShift f proregular).map (homOfLE (i.le_add_right 1)).op =
          (koszulTateFactorizationStage f proregular (i + 1 + 1)).proTransitionHom
            (koszulTateFactorizationStage f proregular (i + 1))
            (koszulTateFactorizationStage_topPower f proregular (i + 1)).symm :=
        Functor.ofOpSequence_map_homOfLE_succ _ (i + 1)
      rw [h]
      exact proTransitionHom_downHom _ _ _ (one_le_koszulTateFactorizationPower f proregular _)

/-- The components of `koszulTateDown` are the maps `Aᵢ₊₁ → K_{nᵢ₊₁}`. -/
@[simp]
theorem koszulTateDown_app (i : ℕᵒᵖ) :
    (koszulTateDown f proregular).app i =
      (koszulTateFactorizationStage f proregular (i.unop + 1)).downHom :=
  rfl

/-- **The augmentation `(Aᵢ)ᵢ → (R/(f₁^{nᵢ₊₁}, …, f_r^{nᵢ₊₁}))ᵢ` of the Tate system**, with
components the augmentations of the factorizations. -/
def koszulTateAug : koszulTateDGASystem f proregular ⟶ koszulTateQuotientSystem f proregular :=
  NatTrans.ofOpSequence (fun i => (koszulTateFactorizationStage f proregular i).augHom)
    fun i => by
      rw [koszulTateDGASystem_map_succ]
      exact proTransitionHom_augHom _ _ _

/-- The components of `koszulTateAug` are the augmentations `Aᵢ → R/(f₁^{nᵢ₊₁}, …)`. -/
@[simp]
theorem koszulTateAug_app (i : ℕᵒᵖ) :
    (koszulTateAug f proregular).app i =
      (koszulTateFactorizationStage f proregular i.unop).augHom :=
  rfl

/-- **Every stage of the Tate system resolves its quotient**: the components of
`koszulTateAug` are quasi-isomorphisms of the underlying cochain complexes. -/
theorem quasiIso_koszulTateAug_app (i : ℕᵒᵖ) :
    QuasiIso ((koszulTateAug f proregular).app i).toCochainMap :=
  (koszulTateFactorizationStage f proregular i.unop).quasiIso_augHom

/-- The composite `K_{nᵢ₊₂} → Aᵢ₊₁ → K_{nᵢ₊₁}` is the Koszul transition homomorphism. -/
theorem koszulTateStage_upHom_downHom (i : ℕ) :
    (koszulTateFactorizationStage f proregular (i + 1)).upHom ≫
        (koszulTateFactorizationStage f proregular (i + 1)).downHom =
      Koszul.powTransition f (one_le_koszulTateFactorizationPower f proregular (i + 1))
        (koszulTateFactorizationPower_lt_succ f proregular (i + 1)).le :=
  upHom_downHom _ _

/-- The composite `Aᵢ₊₁ → K_{nᵢ₊₁} → Aᵢ` is the transition homomorphism of the Tate system. -/
theorem koszulTateStage_downHom_upHom (i : ℕ) :
    (koszulTateFactorizationStage f proregular (i + 1)).downHom ≫
        (koszulTateFactorizationStage f proregular i).upHom =
      (koszulTateFactorizationStage f proregular (i + 1)).proTransitionHom
        (koszulTateFactorizationStage f proregular i)
        (koszulTateFactorizationStage_topPower f proregular i).symm :=
  hom_eq_of_toAlgebraHom_eq rfl

/-- **The Tate and Koszul systems are pro-isomorphic, on the side of the Tate system**: the
component of `koszulTateDown` at `i` followed by that of `koszulTateUp` is the transition
homomorphism `Aᵢ₊₁ → Aᵢ`. -/
theorem koszulTateDown_app_koszulTateUp_app (i : ℕ) :
    (koszulTateDown f proregular).app (Opposite.op i) ≫
        (koszulTateUp f proregular).app (Opposite.op i) =
      (koszulTateDGASystem f proregular).map (homOfLE (i.le_add_right 1)).op := by
  rw [koszulTateDGASystem_map_succ]
  exact koszulTateStage_downHom_upHom f proregular i

/-- **The Tate and Koszul systems are pro-isomorphic, on the side of the Koszul system**: the
component of `koszulTateUp` at `i + 1` followed by that of `koszulTateDown` at `i` is the
transition homomorphism `K_{nᵢ₊₂} → K_{nᵢ₊₁}`. -/
theorem koszulTateUp_app_koszulTateDown_app (i : ℕ) :
    (koszulTateUp f proregular).app (Opposite.op (i + 1)) ≫
        (koszulTateDown f proregular).app (Opposite.op i) =
      (koszulTateKoszulSystem f proregular).map (homOfLE (i.le_add_right 1)).op :=
  koszulTateStage_upHom_downHom f proregular i

end DividedPowers.TateResolution

end
