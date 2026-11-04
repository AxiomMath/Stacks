module

public import StacksFrontier.RingTheory.Restricted.RigEtale
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Annihilation
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SmulIdModule

/-!
# Rig-étaleness is annihilation of the cohomology: the link (1) ⇔ (3) of Stacks 0AJU

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`, so
that the completed naive cotangent complex is the two-term complex
`NL^∧_{B/A} = (J / J² --d--> ⨁ i, B dxᵢ)`.  Two of the equivalent conditions of Stacks 0AJU
are

* (1) `B` is rig-étale over `(A, I)` — a power of `I` annihilates `NL^∧_{B/A}` **in the derived
  category** `D(B)` (Stacks 0GAY);
* (3) a power of `I` annihilates the two **cohomology modules** `H⁻¹ = ker d` and
  `H⁰ = coker d`.

This file proves that equivalence.  It is not a formality: annihilating the identity of a
complex in `D(B)` is strictly stronger than annihilating its cohomology, and the gap is a
null-homotopy.  What closes it is that `NL^∧_{B/A}` has two terms with the degree-`0` term
free, so a scalar acting by zero in `D(B)` is the same as one realised by an honest `B`-linear
`σ : ⨁ i, B dxᵢ → J / J²` with `σ ∘ d = f · id` and `d ∘ σ = f · id` — which is exactly
`Rig.smul_id_eq_zero_of_differential_section` and
`Rig.exists_differential_section_of_smul_id_eq_zero`.  So the whole content of the link is the
passage between such a `σ` and annihilation of the kernel and the cokernel:

* **(3) ⇒ (1).**  Let `r` kill `ker d` and let `s` kill `coker d`.  Then `s · (⨁ i, B dxᵢ)`
  lies in the image of `d`, so — `⨁ i, B dxᵢ` being projective — `s · id` lifts to a `B`-linear
  `h : ⨁ i, B dxᵢ → J / J²` with `d ∘ h = s · id`.  Put `σ = r · h`.  Then `d ∘ σ = (r s) · id`
  outright, and `σ ∘ d = (r s) · id` because `h (d x) − s x` lies in `ker d`, where the factor
  `r` kills it.  The exponent therefore **doubles**: annihilation of the cohomology by `IᶜB`
  gives rig-étaleness with `I^{2c}`.
* **(1) ⇒ (3).**  Read the two identities satisfied by `σ` on elements: `σ (d x) = f x` with
  `d x = 0` gives `f x = 0`, and `d (σ y) = f y` puts `f y` in the image of `d`.  The exponent
  is **unchanged**.

Only one presentation is used: that rig-étaleness may be tested on any single completed
polynomial presentation is `Rig.isRigEtale_iff`.

## Main definitions

* `Rig.smulIdZeroIdeal`: the ideal of scalars acting by zero on a fixed object of an
  `S`-linear category.

## Main results

* `Rig.exists_split_of_ker_coker_annihilated`: a two-sided splitting of a linear map whose
  kernel and cokernel are annihilated, the target being projective.
* `Rig.isRigEtale_of_annihilatesCohomology`: (3) ⇒ (1) in the library's
  `NaiveCotangent.AnnihilatesCohomology` form, which is the form the transports of
  `StacksFrontier.RingTheory.Rig.NaiveCotangent.Annihilation` produce.
* `Rig.isRigEtale_iff_exists_annihilator_cohomology`: **Stacks 0AJU, (1) ⇔ (3)**.

## Implementation notes

Nothing here touches the universe lifts or the term identifications of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`: the two directions of the passage between
a module-level null-homotopy and `f • 𝟙 = 0` in `D(B)` are already available in
`StacksFrontier.RingTheory.Rig.NaiveCotangent.SmulIdModule`, and this file consumes them.

Annihilation of the identity is additive in the scalar, so the scalars annihilating a fixed
object form an ideal; `Rig.smulIdZeroIdeal` records that, which is what turns the statement
"every product `r s` of elements of `IᶜB` acts by zero" into "`I^{2c}B` acts by zero" with no
element-level bookkeeping — an arbitrary element of `I^{2c}B` is only a *sum* of such products.

The two cohomology modules are named as the kernel and the cokernel of the differential rather
than through `NaiveCotangent.H₁` and `NaiveCotangent.H₀`, because that is the shape the
source's condition (3) has and the shape `Rig.isRigEtale_iff`'s consumers already use; the
bridge to the `AnnihilatesCohomology` structure is `Rig.isRigEtale_of_annihilatesCohomology`.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0AJR](https://stacks.math.columbia.edu/tag/0AJR)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **A two-sided splitting of a map with annihilated kernel and cokernel.**  If `r`
annihilates `ker d` and `s` carries the target into the image of `d`, and the target is
projective, then a single linear `σ` realises multiplication by `r * s` on both the source and
the target against `d`.

The lift of `s · id` along `d` exists by projectivity; multiplying it by `r` makes it well
behaved on the source as well, because the discrepancy lies in `ker d`. -/
public theorem exists_split_of_ker_coker_annihilated {S : Type*} [CommRing S]
    {M : Type*} {N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module.Projective S N] (d : M →ₗ[S] N) {r s : S}
    (hr : ∀ x ∈ LinearMap.ker d, r • x = 0)
    (hs : ∀ y : N, s • y ∈ LinearMap.range d) :
    ∃ σ : N →ₗ[S] M, (∀ x, σ (d x) = (r * s) • x) ∧ ∀ y, d (σ y) = (r * s) • y := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property d.rangeRestrict
    (((s • LinearMap.id : N →ₗ[S] N)).codRestrict (LinearMap.range d) (fun y => hs y))
    (by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩)
  have hhy : ∀ y, d (h y) = s • y := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun hh y)
  refine ⟨r • h, ?_, ?_⟩
  · intro x
    have hmem : h (d x) - s • x ∈ LinearMap.ker d := by
      simp only [LinearMap.mem_ker, map_sub, hhy, map_smul, sub_self]
    have hz := hr _ hmem
    rw [smul_sub, sub_eq_zero] at hz
    simpa [mul_smul] using hz
  · intro y
    rw [LinearMap.smul_apply, map_smul, hhy, smul_smul]

/-- **The scalars acting by zero on a fixed object form an ideal.**  Annihilation of the
identity of `X` is additive in the scalar and stable under multiplication, so the condition
`r • 𝟙 X = 0` cuts out an ideal.  This is what lets a statement about *products* `r * s` be
promoted to one about the ideal `𝔞 * 𝔟`, whose elements are only sums of such products. -/
public def smulIdZeroIdeal {S : Type*} [CommRing S] {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear S C] (X : C) : Ideal S where
  carrier := {r | r • 𝟙 X = 0}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb =>
    have ha' : a • 𝟙 X = 0 := ha
    have hb' : b • 𝟙 X = 0 := hb
    (by rw [add_smul, ha', hb', add_zero] : (a + b) • 𝟙 X = 0)
  smul_mem' := fun c {x} hx =>
    have hx' : x • 𝟙 X = 0 := hx
    (by rw [smul_eq_mul, mul_smul, hx', smul_zero] : (c • x) • 𝟙 X = 0)

/-- Membership in `Rig.smulIdZeroIdeal` is the annihilation of the identity. -/
public theorem mem_smulIdZeroIdeal {S : Type*} [CommRing S] {C : Type*} [Category C]
    [Preadditive C] [CategoryTheory.Linear S C] {X : C} {r : S} :
    r ∈ smulIdZeroIdeal (S := S) X ↔ r • 𝟙 X = 0 :=
  Iff.rfl

/-- The `c`-th power of `B.adicIdeal` is the extension of `I ^ c` to `B`. -/
private theorem adicIdeal_pow_eq_map {A : Type u} [CommRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (c : ℕ) :
    B.adicIdeal ^ c = (I ^ c).map (algebraMap A B.carrier) :=
  (Ideal.map_pow (algebraMap A B.carrier) I c).symm

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Stacks 0AJU, (3) ⇒ (1), in the library's `AnnihilatesCohomology` form.**  If `IᶜB`
annihilates both cohomology modules of the completed naive cotangent complex of one completed
polynomial presentation, then `B` is rig-étale over `(A, I)`.

The exponent doubles: `I^{2c}B` is generated by the products `r * s` with `r, s ∈ IᶜB`, and for
each such product `Rig.exists_split_of_ker_coker_annihilated` builds a module-level
null-homotopy, which `Rig.smul_id_eq_zero_of_differential_section` turns into annihilation in
`D(B)`.  That the scalars so annihilating form an ideal is `Rig.smulIdZeroIdeal`, and that a
single presentation suffices is `Rig.isRigEtale_iff`. -/
public theorem isRigEtale_of_annihilatesCohomology (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) {c : ℕ}
    (h : NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
      (completedNaiveCotangentComplex B P).twoTerm) :
    IsRigEtale B := by
  set K := completedNaiveCotangentComplex B P
  refine (isRigEtale_iff B P).mpr ⟨2 * c, fun a ha => ?_⟩
  have hle : B.adicIdeal ^ (2 * c) ≤
      smulIdZeroIdeal ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
        K.cochainComplex) := by
    rw [two_mul, pow_add]
    refine Ideal.mul_le.mpr fun r hr s hs => ?_
    obtain ⟨σ, hσd, hdσ⟩ := exists_split_of_ker_coker_annihilated K.differential
      (fun x hx => h.smul_eq_zero_of_d_eq_zero hr (X := K.twoTerm) hx)
      (fun y => h.smul_mem_range hs y)
    exact smul_id_eq_zero_of_differential_section B P (r * s) σ hσd hdσ
  refine hle ?_
  rw [adicIdeal_pow_eq_map]
  exact Ideal.mem_map_of_mem _ ha

/-- **Stacks 0AJU, (1) ⇔ (3).**  For an `I`-adically complete `A`-algebra `B` of finite type
modulo `I` over a Noetherian ring `A`, and any completed polynomial presentation
`B = A⟨x₁, …, x_r⟩ / J`, rig-étaleness of `B` over `(A, I)` is equivalent to the existence of a
`c` with `IᶜB` annihilating both cohomology modules `H⁻¹(NL^∧_{B/A}) = ker d` and
`H⁰(NL^∧_{B/A}) = coker d`.

Condition (1) is annihilation of the complex *in the derived category* and condition (3) is
annihilation of its cohomology, which is weaker for a general complex; the two agree here
because `NL^∧_{B/A}` has two terms and its degree-`0` term is free, so the annihilating scalar
is realised by an honest two-sided splitting of the differential.  Passing from (3) to (1) costs
a squaring of the ideal and passing back costs nothing, which is why the statement is an
equivalence of the *existence* of an exponent rather than of a fixed one. -/
@[stacks 0AJU "(1) iff (3)"]
public theorem isRigEtale_iff_exists_annihilator_cohomology
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    IsRigEtale B ↔
      ∃ c : ℕ,
        (I ^ c).map (algebraMap A B.carrier) ≤
          Module.annihilator B.carrier
            (LinearMap.ker (completedNaiveCotangentComplex B P).differential) ∧
        (I ^ c).map (algebraMap A B.carrier) ≤
          Module.annihilator B.carrier
            ((Fin P.variableCount → B.carrier) ⧸
              LinearMap.range (completedNaiveCotangentComplex B P).differential) := by
  set K := completedNaiveCotangentComplex B P
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (isRigEtale_iff B P).mp h
    refine ⟨c, Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_,
      Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_⟩
    · obtain ⟨σ, hσd, -⟩ := exists_differential_section_of_smul_id_eq_zero B P
        (algebraMap A B.carrier a) (hc a ha)
      refine Module.mem_annihilator.mpr fun z => ?_
      have hzero : (algebraMap A B.carrier) a • (z : P.extension.Cotangent) = 0 := by
        rw [← hσd z.1, LinearMap.mem_ker.mp z.2, map_zero]
      exact Subtype.ext (by simpa using hzero)
    · obtain ⟨σ, -, hdσ⟩ := exists_differential_section_of_smul_id_eq_zero B P
        (algebraMap A B.carrier a) (hc a ha)
      refine Module.mem_annihilator.mpr fun z => ?_
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range K.differential) z
      have hz : Submodule.mkQ (LinearMap.range K.differential)
          (algebraMap A B.carrier a • y) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact ⟨σ y, hdσ y⟩
      rwa [map_smul] at hz
  · rintro ⟨c, hker, hcoker⟩
    have hle := (adicIdeal_pow_eq_map B c).le
    refine isRigEtale_of_annihilatesCohomology B P (c := c) ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
    · refine Submodule.mem_annihilator.mpr fun x hx => ?_
      exact congrArg Subtype.val
        (Module.mem_annihilator.mp (hker (hle hr)) (⟨x, hx⟩ : LinearMap.ker K.differential))
    · exact Module.mem_annihilator.mpr (Module.mem_annihilator.mp (hcoker (hle hr)))

end Rig

end
