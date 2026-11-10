module

public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSyntomicOpen
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalTable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.Deformation.Examples.Geometric.Smoothing
public import StacksFrontier.RingTheory.CompleteIntersection.FieldExtension

/-!
# The universal finite étale locus

The universal finite free family `pi_d : Y_d ⟶ X_d` of rank `d` (Tag 0FKZ) has an open locus
`U'_d` in its base `X_d` over which it is étale, and that open subscheme is dense in the open
`U_d` over which the family is syntomic (Tag 0FL0). This is Tag 0FL2.

## Main definitions

* `AlgebraicGeometry.universalEtaleOpen` is the open subscheme `U'_d` of `X_d`.

## Main results

* `AlgebraicGeometry.factorsThrough_universalEtaleOpen_iff`: a morphism `g : T ⟶ X_d` factors
  through `U'_d` exactly when the base change of the family along `g` is étale.
* `AlgebraicGeometry.universalEtaleOpen_le_universalSyntomicOpen`: `U'_d ⊆ U_d`.
* `AlgebraicGeometry.dense_universalEtaleOpen_in_universalSyntomicOpen`: `U'_d` is dense in
  `U_d`.

## Implementation notes

As for the syntomic locus of Tag 0FL0, the étale locus is defined as the interior of the set of
points of `X_d` over which every point of the fibre is étale; that set is already open, because
the family is finite and hence closed, which is
`AlgebraicGeometry.universalEtaleOpen_coe_eq`.

Density is proved by deforming, rather than by the henselization of the source. Let
`u : Spec(k) ⟶ U_d` be a point of the syntomic locus with values in a field. The base change of
the family along `u` is a syntomic `k`-algebra `B`, free of rank `d` on a basis beginning with
`1`, hence a finite-dimensional local complete intersection; Tag 0E7W
(`Deformation.Examples.Smoothing.exists_finite_powerSeries_specialFiber_etale_genericFiber`)
produces a finite flat `k⟦t⟧`-algebra `B'` with special fibre `B` and étale generic fibre. The
local ring `k⟦t⟧` plays the role of the source's local domain `A'` with residue field `k`.
Flatness lifts the basis of `B` to a basis of `B'` beginning with `1`, by
`Module.IsLocalRing.linearCombination_bijective_of_flat`, so the multiplication table of `B'` is
a morphism `Spec(k⟦t⟧) ⟶ X_d` restricting to `u` at the closed point; the generic point maps
into `U'_d` because the generic fibre is étale, and it specializes to the closed point, so `u`
lies in the closure of `U'_d`.

## References

* [Stacks Project, Tag 0FL2](https://stacks.math.columbia.edu/tag/0FL2)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
* [Stacks Project, Tag 02GQ](https://stacks.math.columbia.edu/tag/02GQ)
* [Stacks Project, Tag 0E7W](https://stacks.math.columbia.edu/tag/0E7W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.FiniteFreeAlgebra

universe u v

namespace AlgebraicGeometry

open scoped BigOperators
open scoped TensorProduct

/-- A syntomic algebra over a field is a local complete intersection. -/
private theorem syntomic_field_algebra_isLocalCompleteIntersection (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] (hA : Algebra.Syntomic k A) :
    IsLocalCompleteIntersection k A := by
  let : Algebra A ((⊥ : Ideal k).Fiber A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.IsPushout k (⊥ : Ideal k).ResidueField A ((⊥ : Ideal k).Fiber A) :=
    inferInstance
  exact (Algebra.IsPushout.isLocalCompleteIntersection_iff k
    (⊥ : Ideal k).ResidueField A ((⊥ : Ideal k).Fiber A)).mp
    (hA.isLocalCompleteIntersection_fiber (⊥ : Ideal k))

/-- The residue map of a power series ring sends a constant to its own class. -/
private theorem residue_powerSeries_C {k : Type*} [Field k] (a : k) :
    PowerSeries.residueFieldOfPowerSeries.symm a =
      IsLocalRing.residue (PowerSeries k) (PowerSeries.C a) := by
  apply PowerSeries.residueFieldOfPowerSeries.injective
  simp only [RingEquiv.apply_symm_apply]
  change a = (((Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries.C a)))
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  simp

/-- Over a local ring, a basis of the closed fibre of a finite flat algebra beginning with `1`
lifts to a basis of the algebra beginning with `1`. -/
private theorem exists_basis_lift_of_flat {R B : Type*} [CommRing R] [IsLocalRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Module.Flat R B] {d : ℕ} [NeZero d]
    (bT : Module.Basis (Fin d) (IsLocalRing.ResidueField R)
      (TensorProduct R (IsLocalRing.ResidueField R) B))
    (hbT : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 : B) = bT 0) :
    ∃ b' : Module.Basis (Fin d) R B, b' 0 = 1 ∧
      ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] b' i = bT i := by
  classical
  let q : B →ₗ[R] TensorProduct R (IsLocalRing.ResidueField R) B :=
    TensorProduct.mk R _ _ 1
  have hq : Function.Surjective q :=
    TensorProduct.mk_surjective R B _ IsLocalRing.residue_surjective
  let v : Fin d → B := fun i => if i = 0 then 1 else (hq (bT i)).choose
  have hv (i) : q (v i) = bT i := by
    by_cases hi : i = 0
    · subst i
      simpa [q, v] using hbT
    · simpa [v, hi] using (hq (bT i)).choose_spec
  have hbij := Module.IsLocalRing.linearCombination_bijective_of_flat v (by
    rw [show q ∘ v = bT from funext hv]
    convert bT.repr.symm.bijective using 1
    funext z
    exact (bT.repr_symm_apply z).symm)
  let e := LinearEquiv.ofBijective (Finsupp.linearCombination R v) hbij
  let b' := (Finsupp.basisSingleOne (R := R) (ι := Fin d)).map e
  refine ⟨b', by simp [b', e, v], fun i ↦ ?_⟩
  simpa [b', e, q, Module.Basis.map_apply, LinearEquiv.ofBijective_apply,
    Finsupp.linearCombination_single, one_smul] using hv i

/-- A basis of the special fibre of a finite flat algebra over a power series ring in one
variable lifts to a basis of the algebra, with the unit lifting to the unit. -/
private theorem exists_basis_lift_powerSeries {k B : Type*} [Field k] [CommRing B]
    [Algebra (PowerSeries k) B] [Algebra k B] [IsScalarTower k (PowerSeries k) B]
    [Module.Finite (PowerSeries k) B] [Module.Flat (PowerSeries k) B]
    {d : ℕ} [NeZero d]
    (b : Module.Basis (Fin d) k
      (B ⧸ Ideal.span ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)))
    (hb : b 0 = 1) :
    ∃ b' : Module.Basis (Fin d) (PowerSeries k) B, b' 0 = 1 ∧
      ∀ i, Ideal.Quotient.mk _ (b' i) = b i := by
  let R := PowerSeries k
  let m := IsLocalRing.maximalIdeal R
  let J := m.map (algebraMap R B)
  have hJ : J = Ideal.span ({algebraMap R B PowerSeries.X} : Set B) := by
    dsimp [J, m, R]
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton]
  let eQ := Ideal.quotientEquivAlgOfEq k hJ
  let bQ : Module.Basis (Fin d) k (B ⧸ J) := b.map eQ.symm.toLinearEquiv
  let ρ := PowerSeries.residueFieldOfPowerSeries (k := k)
  let : Algebra (IsLocalRing.ResidueField R) (B ⧸ J) :=
    (inferInstance : Algebra (R ⧸ m) (B ⧸ m.map (algebraMap R B)))
  let bκ : Module.Basis (Fin d) (IsLocalRing.ResidueField R) (B ⧸ J) :=
    bQ.mapCoeffs ρ.symm (by
      intro c x
      rw [show ρ.symm c = IsLocalRing.residue R (PowerSeries.C c) from residue_powerSeries_C c]
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk m (PowerSeries.C c) • Ideal.Quotient.mk J y = _
      rw [Ideal.Quotient.mk_smul_mk_quotient_map_quotient]
      rw [show algebraMap R B (PowerSeries.C c) = algebraMap k B c from
        (IsScalarTower.algebraMap_apply k R B c).symm]
      simp only [map_mul, Ideal.Quotient.mk_algebraMap, Algebra.smul_def]
      rfl)
  let eT : (B ⧸ J) ≃ₐ[IsLocalRing.ResidueField R]
      TensorProduct R (IsLocalRing.ResidueField R) B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B m
  let bT := bκ.map eT.toLinearEquiv
  have hbT : (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 : B) = bT 0 := by
    change 1 ⊗ₜ[R] (1 : B) = eT (bκ 0)
    simp only [bκ, Module.Basis.mapCoeffs_apply, bQ, Module.Basis.map_apply,
      AlgEquiv.toLinearEquiv_apply, hb, map_one]
    rfl
  obtain ⟨b', hb', hlift⟩ := exists_basis_lift_of_flat bT hbT
  refine ⟨b', hb', fun i ↦ ?_⟩
  have h' : Ideal.Quotient.mk J (b' i) = bQ i := by
    apply eT.injective
    change (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] b' i = eT (bQ i)
    simpa [bT, bκ, Module.Basis.map_apply, Module.Basis.mapCoeffs_apply,
      AlgEquiv.toLinearEquiv_apply] using hlift i
  change eQ (Ideal.Quotient.mk J (b' i)) = b i
  rw [h']
  exact eQ.apply_symm_apply (b i)

/-- The special fibre of a power series algebra receives a scalar through the constant
coefficient. -/
private theorem quotient_powerSeries_algebraMap {k B : Type*} [Field k] [CommRing B]
    [Algebra (PowerSeries k) B] [Algebra k B] [IsScalarTower k (PowerSeries k) B]
    (r : PowerSeries k) :
    let J := Ideal.span ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)
    Ideal.Quotient.mk J (algebraMap (PowerSeries k) B r) =
      algebraMap k (B ⧸ J) (PowerSeries.constantCoeff r) := by
  dsimp only
  rw [← Ideal.Quotient.mk_algebraMap, IsScalarTower.algebraMap_apply k (PowerSeries k) B]
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub]
  have hr : r - PowerSeries.C (PowerSeries.constantCoeff r) ∈
      IsLocalRing.maximalIdeal (PowerSeries k) := by
    rw [← PowerSeries.ker_coeff_eq_max_ideal]
    simp [RingHom.mem_ker]
  have hm := Ideal.mem_map_of_mem (algebraMap (PowerSeries k) B) hr
  rwa [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton] at hm

/-- The generic point of `Spec K` maps under `Spec R ← Spec K` to a point specializing to every
point of `Spec R`, when `R → K` is injective. -/
private theorem spec_map_bot_specializes {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    (h : Function.Injective (algebraMap R K)) (p : Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (algebraMap R K))
      (⟨⊥, inferInstance⟩ : Spec (CommRingCat.of K)) ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes _ _).mp
  change RingHom.ker (algebraMap R K) ≤ p.asIdeal
  rw [(RingHom.injective_iff_ker_eq_bot _).mp h]
  exact bot_le

variable (d : ℕ) [NeZero d]

/-- A syntomic algebra over a field with a basis beginning with `1` is the special fibre of a
finite flat `k⟦t⟧`-algebra with étale generic fibre, on a basis lifting the given one. -/
private theorem exists_powerSeries_deformation_basis {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (hA : Algebra.Syntomic k A) (bA : Module.Basis (Fin d) k A) (hbA : bA 0 = 1) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B) (_ : Algebra k B)
      (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Algebra.Etale (LaurentSeries k) (TensorProduct (PowerSeries k) (LaurentSeries k) B))
      (e : (B ⧸ Ideal.span ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)) ≃ₐ[k] A)
      (b : Module.Basis (Fin d) (PowerSeries k) B), b 0 = 1 ∧
        ∀ j, e (Ideal.Quotient.mk _ (b j)) = bA j := by
  let : FiniteDimensional k A := bA.finiteDimensional_of_finite
  obtain ⟨B, hB, aB, akB, htower, hfinite, hflat, ⟨e⟩, hetale⟩ :=
    Deformation.Examples.Smoothing.exists_finite_powerSeries_specialFiber_etale_genericFiber
      k A (syntomic_field_algebra_isLocalCompleteIntersection k A hA)
  let := hB
  let := aB
  let := akB
  let := htower
  let := hfinite
  let := hflat
  obtain ⟨b, hb, hbe⟩ := exists_basis_lift_powerSeries (bA.map e.symm.toLinearEquiv)
    (by simp only [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, hbA, map_one])
  refine ⟨B, hB, aB, akB, htower, hetale, e, b, hb, fun j ↦ ?_⟩
  rw [hbe j]
  exact e.apply_symm_apply (bA j)

/-- Pulling back the morphism classifying a multiplication table along `i` gives the table of a
basis that a ring map compatible with `i` carries the first basis to. -/
private theorem representation_equiv_comp_symm_ofBasis {T T' : Scheme.{u}} (i : T ⟶ T')
    {A B : Type u} [CommRing A] [CommRing B] [Algebra Γ(T, ⊤) A] [Algebra Γ(T', ⊤) B]
    (bB : Module.Basis (Fin d) Γ(T', ⊤) B) (hbB : bB 0 = 1)
    (bA : Module.Basis (Fin d) Γ(T, ⊤) A) (hbA : bA 0 = 1) (q : B →+* A)
    (hq : ∀ r, q (algebraMap Γ(T', ⊤) B r) = algebraMap Γ(T, ⊤) A (i.appTop.hom r))
    (hqb : ∀ j, q (bB j) = bA j) :
    (representation.{u} d).equiv T
        (i ≫ ((representation.{u} d).equiv T').symm (ofBasis bB hbB)) =
      ofBasis bA hbA := by
  rw [← (representation.{u} d).naturality]
  rw [Equiv.apply_symm_apply]
  exact ofBasis_map i.appTop.hom q hq bB hbB bA hbA hqb

/-- The set of points of `X_d` over which the universal finite free family of rank `d` is étale
at every point of the fibre. -/
def universalEtaleLocus : Set (scheme.{u} d) :=
  {x | ∀ y : universalTotalScheme.{u} d (universalAlgebraStructure d),
    universalFamily.{u} d (universalAlgebraStructure d) y = x →
      EtaleAt (universalFamily.{u} d (universalAlgebraStructure d)) y}

/-- **Stacks Project, Tag 0FL2.** The open subscheme `U'_d` of the base `X_d` of the universal
finite free family of rank `d` over which the family is étale.

It is the interior of `AlgebraicGeometry.universalEtaleLocus`; that set is already open, by
`AlgebraicGeometry.universalEtaleLocus_isOpen`. -/
@[stacks 0FL2 "the étale open subscheme"]
def universalEtaleOpen : (scheme.{u} d).Opens :=
  ⟨interior (universalEtaleLocus.{u} d), isOpen_interior⟩

/-- The locus of `AlgebraicGeometry.universalEtaleLocus` is open: its complement is the image of
the closed non-étale locus under the universal family, which is a closed map because the family
is finite. -/
theorem universalEtaleLocus_isOpen : IsOpen (universalEtaleLocus.{u} d) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  have hprops := universalFamily_isFinite_flat_locallyOfFinitePresentation.{u} d
  have : IsFinite π := hprops.1
  have : IsIntegralHom π := ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType π).mp hprops.1).1
  have : UniversallyClosed π :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom).mp inferInstance |>.1
  have hEq : universalEtaleLocus.{u} d = (π '' {y | EtaleAt π y}ᶜ)ᶜ := by
    ext b
    exact ⟨fun hb ⟨y, hy, hyb⟩ ↦ hy (hb y hyb),
      fun hb y hyb ↦ Classical.byContradiction fun hyW ↦ hb ⟨y, hyW, hyb⟩⟩
  rw [hEq]
  exact (π.isClosedMap _ (isOpen_setOf_etaleAt π).isClosed_compl).isOpen_compl

/-- The open subscheme `U'_d` is the whole locus where the universal family is étale on the
fibre: no interior needs to be taken. -/
theorem universalEtaleOpen_coe_eq :
    ((universalEtaleOpen.{u} d : (scheme.{u} d).Opens) : Set (scheme.{u} d)) =
      universalEtaleLocus.{u} d :=
  interior_eq_iff_isOpen.mpr (universalEtaleLocus_isOpen.{u} d)

/-- **Stacks Project, Tag 0FL2.** A morphism `g : T ⟶ X_d` to the base of the universal finite
free family of rank `d` factors through the open subscheme
`AlgebraicGeometry.universalEtaleOpen` exactly when the base change of the family along `g` is
étale. -/
@[stacks 0FL2 "universal property of the étale open"]
theorem factorsThrough_universalEtaleOpen_iff (T : Scheme.{u}) (g : T ⟶ scheme.{u} d) :
    (∃ ĝ : T ⟶ (universalEtaleOpen.{u} d).toScheme,
        ĝ ≫ (universalEtaleOpen.{u} d).ι = g) ↔
      Etale (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d)) g) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  let U := universalEtaleOpen.{u} d
  let p := pullback.snd π g
  have hprops := universalFamily_isFinite_flat_locallyOfFinitePresentation.{u} d
  have : Flat π := hprops.2.1
  have : LocallyOfFinitePresentation π := hprops.2.2
  have hpull : IsPullback (pullback.fst π g) p π g := IsPullback.of_hasPullback π g
  have hbase := setOf_etaleAt_eq_preimage_of_isPullback hpull (Or.inl ‹Flat π›)
  have hFactor : (∃ ĝ : T ⟶ U.toScheme, ĝ ≫ U.ι = g) ↔ Set.range g.base ⊆ (U : Set _) := by
    refine ⟨?_, fun hg ↦ ⟨IsOpenImmersion.lift U.ι g
      (by simpa only [Scheme.Opens.range_ι] using hg), IsOpenImmersion.lift_fac _ _ _⟩⟩
    rintro ⟨ĝ, hĝ⟩ _ ⟨t, rfl⟩
    have ht : g.base t ∈ Set.range U.ι :=
      ⟨ĝ.base t, by simpa using congrArg (fun k : T ⟶ _ ↦ k.base t) hĝ⟩
    simpa only [Scheme.Opens.range_ι] using ht
  have hRange : Set.range g.base ⊆ (U : Set _) ↔ Etale p := by
    rw [Set.range_subset_iff, etale_iff_forall_etaleAt p]
    show (∀ t : T, g t ∈ (U : Set _)) ↔ ∀ z : (pullback π g : Scheme), EtaleAt p z
    rw [universalEtaleOpen_coe_eq.{u} d]
    have hbaseAt (z : (pullback π g : Scheme)) :
        EtaleAt p z ↔ EtaleAt π ((pullback.fst π g).base z) := by
      simpa using congrArg (fun W : Set (pullback π g : Scheme) ↦ z ∈ W) hbase
    refine ⟨fun hg z ↦ ?_, fun hz t y hy ↦ ?_⟩
    · have hz : π ((pullback.fst π g).base z) = g ((pullback.snd π g).base z) := by
        simpa using congrArg (fun k : pullback π g ⟶ scheme.{u} d ↦ k.base z)
          (pullback.condition (f := π) (g := g))
      exact (hbaseAt z).mpr (hg ((pullback.snd π g).base z) ((pullback.fst π g).base z) hz)
    · obtain ⟨z, hzfst, _⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := π) (g := g) y t hy
      simpa only [hzfst] using (hbaseAt z).mp (hz z)
  exact hFactor.trans hRange

/-- **Stacks Project, Tag 0FL2.** The open subscheme over which the universal finite free family
of rank `d` is étale is contained in the open subscheme over which it is syntomic, because the
family is syntomic at every point at which it is étale. -/
@[stacks 0FL2 "containment in the syntomic open"]
theorem universalEtaleOpen_le_universalSyntomicOpen :
    universalEtaleOpen.{u} d ≤ universalSyntomicOpen.{u} d := by
  intro x hx
  change x ∈ (universalEtaleOpen.{u} d : Set (scheme.{u} d)) at hx
  change x ∈ (universalSyntomicOpen.{u} d : Set (scheme.{u} d))
  rw [universalEtaleOpen_coe_eq.{u} d] at hx
  rw [universalSyntomicOpen_coe_eq.{u} d]
  exact fun y hy ↦ syntomicAt_of_etaleAt _ y (hx y hy)

/-- The universal total scheme is affine. -/
private theorem isAffine_universalTotalScheme :
    IsAffine (universalTotalScheme.{u} d (universalAlgebraStructure d)) := by
  dsimp [universalTotalScheme]
  infer_instance

/-- Over an affine scheme `T`, the global sections of the base change of the universal family
along `f` have a basis beginning with `1` whose multiplication table is `f`. -/
private theorem exists_basis_ofBasis_eq_table {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ scheme.{u} d) :
    letI : Algebra Γ(T, ⊤) Γ(pullback (universalFamily.{u} d (universalAlgebraStructure d)) f, ⊤) :=
      (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d)) f).appTop.hom.toAlgebra
    ∃ (b : Module.Basis (Fin d) Γ(T, ⊤)
        Γ(pullback (universalFamily.{u} d (universalAlgebraStructure d)) f, ⊤)) (hb : b 0 = 1),
      ofBasis b hb = (representation.{u} d).equiv T f := by
  have := isAffine_universalTotalScheme.{u} d
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  exact ⟨_, affinePullbackGammaBasis_zero π f d (universalTotalGammaBasis.{u} d)
    (universalTotalGammaBasis_zero.{u} d),
    affinePullbackGammaBasis_structure_of_map π f (universalTotalGammaBasis.{u} d)
      (universalTotalGammaBasis_zero.{u} d) (universalTotalGammaBasis_structure.{u} d)⟩

/-- A base change of the universal family along a morphism of affine schemes is étale as soon as
its global sections are an étale algebra on a basis realizing the multiplication table of that
morphism. -/
private theorem etale_pullback_of_basis_table
    {T : Scheme.{u}} [IsAffine T] (f : T ⟶ scheme.{u} d)
    {B : Type u} [CommRing B] [Algebra Γ(T, ⊤) B] [Algebra.Etale Γ(T, ⊤) B]
    (b : Module.Basis (Fin d) Γ(T, ⊤) B) (hb : b 0 = 1)
    (h : ofBasis b hb = (representation.{u} d).equiv T f) :
    Etale (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d)) f) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  have := isAffine_universalTotalScheme.{u} d
  let : Algebra Γ(T, ⊤) Γ(pullback π f, ⊤) := (pullback.snd π f).appTop.hom.toAlgebra
  obtain ⟨bP, hbP, hP⟩ := exists_basis_ofBasis_eq_table.{u} d f
  have hEt : Algebra.Etale Γ(T, ⊤) Γ(pullback π f, ⊤) :=
    Algebra.Etale.of_equiv (algEquivOfBasisEq bP b hbP hb (hP.trans h.symm)).symm
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := pullback.snd π f)).mpr hEt

/-- If the generic fibre of an `R`-algebra `B` is étale, then every point of `Spec R` maps into
the closure of the étale open under the morphism classifying the table of a basis of `B`. -/
private theorem mem_closure_universalEtaleOpen_of_etale_genericFiber
    {R K B : Type u} [CommRing R] [Field K] [Algebra R K]
    (hRK : Function.Injective (algebraMap R K)) [CommRing B] [Algebra R B]
    [Algebra.Etale K (TensorProduct R K B)] [Algebra Γ(Spec (CommRingCat.of R), ⊤) B]
    (hB : ∀ r, algebraMap Γ(Spec (CommRingCat.of R), ⊤) B r =
      algebraMap R B ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv r))
    (b : Module.Basis (Fin d) R B) (bR : Module.Basis (Fin d) Γ(Spec (CommRingCat.of R), ⊤) B)
    (hbR : bR 0 = 1) (hbRb : ∀ j, bR j = b j) (p : Spec (CommRingCat.of R)) :
    ((representation.{u} d).equiv (Spec (CommRingCat.of R))).symm (ofBasis bR hbR) p ∈
      closure (universalEtaleOpen.{u} d : Set (scheme.{u} d)) := by
  let U := universalEtaleOpen.{u} d
  let X := scheme.{u} d
  let TR := Spec (CommRingCat.of R)
  let fR : TR ⟶ X := ((representation.{u} d).equiv TR).symm (ofBasis bR hbR)
  let ρR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hb : b 0 = 1 := (hbRb 0).symm.trans hbR
  let TK := Spec (CommRingCat.of K)
  let η : TK ⟶ TR := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let ρK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hη (r : Γ(TR, ⊤)) : ρK (η.appTop.hom r) = algebraMap R K (ρR r) :=
    congrArg (fun φ : Γ(TR, ⊤) ⟶ CommRingCat.of K => φ.hom r)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K)))
  let C := TensorProduct R K B
  let : Algebra Γ(TK, ⊤) K := ρK.toRingHom.toAlgebra
  let : Algebra Γ(TK, ⊤) C := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower Γ(TK, ⊤) K C := by infer_instance
  have : Algebra.Etale Γ(TK, ⊤) K := (RingHom.Etale.of_bijective ρK.bijective).toAlgebra
  have : Algebra.Etale Γ(TK, ⊤) C := Algebra.Etale.comp Γ(TK, ⊤) K C
  let bK := b.baseChange K
  let bG : Module.Basis (Fin d) Γ(TK, ⊤) C := bK.mapCoeffs ρK.symm (by
    intro c y
    change ρK (ρK.symm c) • y = c • y
    rw [RingEquiv.apply_symm_apply])
  have hbG : bG 0 = 1 := by
    simp only [bG, Module.Basis.mapCoeffs_apply, bK, Module.Basis.baseChange_apply, hb]
    rfl
  let qG : B →+* C := Algebra.TensorProduct.includeRight.toRingHom
  have hqG (r : Γ(TR, ⊤)) : qG (algebraMap Γ(TR, ⊤) B r) =
      algebraMap Γ(TK, ⊤) C (η.appTop.hom r) := by
    rw [hB]
    change Algebra.TensorProduct.includeRight (algebraMap R B (ρR r)) =
      algebraMap K C (ρK (η.appTop.hom r))
    rw [hη]
    exact Algebra.TensorProduct.includeRight.commutes (ρR r)
  have hqbG (j : Fin d) : qG (bR j) = bG j := by
    simp only [hbRb, bG, Module.Basis.mapCoeffs_apply, bK, Module.Basis.baseChange_apply]
    rfl
  obtain ⟨gU, hgU⟩ := (factorsThrough_universalEtaleOpen_iff.{u} d TK (η ≫ fR)).mpr
    (etale_pullback_of_basis_table d (η ≫ fR) bG hbG
      (representation_equiv_comp_symm_ofBasis d η bR hbR bG hbG qG hqG hqbG).symm)
  let ξ : TK := ⟨⊥, inferInstance⟩
  have hξ : (η ≫ fR) ξ ∈ (U : Set X) := by
    have hval := congrArg (fun h : TK ⟶ X => h ξ) hgU
    rw [← hval]
    exact (gU ξ).property
  have hsp : η ξ ⤳ p := spec_map_bot_specializes hRK p
  exact closure_mono (Set.singleton_subset_iff.mpr hξ)
    (specializes_iff_mem_closure.mp (hsp.map fR.continuous))

/-- A morphism from an affine scheme with a field of global sections to the base of the universal
family, along which the family is syntomic, lands in the closure of the étale open. -/
private theorem apply_mem_closure_universalEtaleOpen_of_syntomic {T : Scheme.{u}} [IsAffine T]
    (hT : IsField Γ(T, ⊤)) (f₀ : T ⟶ scheme.{u} d)
    (hsyn : Syntomic (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d)) f₀))
    (t : T) : f₀ t ∈ closure (universalEtaleOpen.{u} d : Set (scheme.{u} d)) := by
  let π := universalFamily.{u} d (universalAlgebraStructure d)
  have := isAffine_universalTotalScheme.{u} d
  let k := Γ(T, ⊤)
  let : Field k := hT.toField
  let A := Γ(pullback π f₀, ⊤)
  let : Algebra k A := (pullback.snd π f₀).appTop.hom.toAlgebra
  have hsynA : Algebra.Syntomic k A := algebraSyntomic_of_affineSyntomic (pullback.snd π f₀) hsyn
  obtain ⟨bA, hbA, htableA⟩ := exists_basis_ofBasis_eq_table.{u} d f₀
  obtain ⟨B, _, _, _, _, _, eSpecial, b, hb, hbe⟩ :=
    exists_powerSeries_deformation_basis d hsynA bA hbA
  let R := PowerSeries k
  let TR := Spec (CommRingCat.of R)
  let ρR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let : Algebra Γ(TR, ⊤) B := Algebra.compHom B ρR.toRingHom
  let bR : Module.Basis (Fin d) Γ(TR, ⊤) B := b.mapCoeffs ρR.symm (by
    intro c y
    change ρR (ρR.symm c) • y = c • y
    rw [RingEquiv.apply_symm_apply])
  have hbR : bR 0 = 1 := by simpa [bR, Module.Basis.mapCoeffs_apply] using hb
  have hbRb (j : Fin d) : bR j = b j := Module.Basis.mapCoeffs_apply _ _ _ _
  let i : T ⟶ TR := ΓSpec.adjunction.homEquiv T (.op (CommRingCat.of R))
    (CommRingCat.ofHom (R := R) (S := k) (PowerSeries.constantCoeff (R := k))).op
  have hi (r : Γ(TR, ⊤)) : i.appTop.hom r = PowerSeries.constantCoeff (ρR r) := by
    have h := congrArg (fun φ : CommRingCat.of R ⟶ Γ(T, ⊤) => φ.hom (ρR r))
      (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        (X := T) (CommRingCat.ofHom (R := R) (S := k) (PowerSeries.constantCoeff (R := k))))
    change i.appTop.hom (ρR.symm (ρR r)) = PowerSeries.constantCoeff (ρR r) at h
    simpa only [RingEquiv.symm_apply_apply] using h
  let J := Ideal.span ({algebraMap (PowerSeries k) B PowerSeries.X} : Set B)
  let q : B →+* A := eSpecial.toRingHom.comp (Ideal.Quotient.mk J)
  have hq (r : Γ(TR, ⊤)) :
      q (algebraMap Γ(TR, ⊤) B r) = algebraMap k A (i.appTop.hom r) := by
    change eSpecial (Ideal.Quotient.mk J (algebraMap R B (ρR r))) = _
    rw [quotient_powerSeries_algebraMap, eSpecial.commutes, hi]
  have hqb (j : Fin d) : q (bR j) = bA j := by
    rw [hbRb]
    exact hbe j
  have hcomm : i ≫ ((representation.{u} d).equiv TR).symm (ofBasis bR hbR) = f₀ :=
    ((representation.{u} d).equiv T).injective
      ((representation_equiv_comp_symm_ofBasis d i bR hbR bA hbA q hq hqb).trans htableA)
  rw [← hcomm]
  exact mem_closure_universalEtaleOpen_of_etale_genericFiber d (R := R) (K := LaurentSeries k)
    (IsFractionRing.injective R _) (fun _ ↦ rfl) b bR hbR hbRb (i t)

/-- **Stacks Project, Tag 0FL2.** The open subscheme `U'_d` of the base of the universal finite
free family of rank `d` over which that family is étale is dense in the open subscheme `U_d` over
which it is syntomic. -/
@[stacks 0FL2 "density in the syntomic open"]
theorem dense_universalEtaleOpen_in_universalSyntomicOpen :
    Dense ((universalSyntomicOpen.{u} d).ι ⁻¹'
      (↑(universalEtaleOpen.{u} d) : Set (scheme.{u} d))) := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_iff_forall.mpr fun z ↦ ?_
  let S := universalSyntomicOpen.{u} d
  let X := scheme.{u} d
  let x : X := S.ι.base z
  have hrange : Set.range (X.fromSpecResidueField x).base ⊆ Set.range S.ι := by
    rintro y ⟨t, rfl⟩
    exact ⟨z, (Scheme.fromSpecResidueField_apply x t).symm⟩
  have hsyn := (factorsThrough_universalSyntomicOpen_iff.{u} d _ (X.fromSpecResidueField x)).mp
    ⟨IsOpenImmersion.lift S.ι _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  have hT : IsField Γ(Spec (X.residueField x), ⊤) := MulEquiv.isField (Field.toIsField _)
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv
  have hx := apply_mem_closure_universalEtaleOpen_of_syntomic d hT _ hsyn ⟨⊥, inferInstance⟩
  rw [show X.fromSpecResidueField x ⟨⊥, inferInstance⟩ = x from
    Scheme.fromSpecResidueField_apply x _] at hx
  exact S.ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hx

end AlgebraicGeometry

end
