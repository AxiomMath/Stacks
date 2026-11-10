module

public import StacksFrontier.RingTheory.Derivation.Extension
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.Category
public import StacksFrontier.RingTheory.Rig.Deformation
public import StacksFrontier.RingTheory.Rig.PresentationGenerators

/-!
# The completed naive cotangent complex

Let `A` be a Noetherian ring, let `I` be an ideal of `A`, and let `B` be an `I`-adically
complete `A`-algebra of finite type modulo `I`. Writing `B = A[x₁, …, xᵣ]^ / J` for a
presentation of `B` as a quotient of a completed polynomial algebra, the completed naive
cotangent complex of that presentation is the two-term cochain complex

`J / J² → ⨁ i, B dxᵢ`,

with the conormal module in degree `-1` and the free module in degree `0`. Its differential
sends the class of a restricted power series `g ∈ J` to the tuple of the images in `B` of
its formal partial derivatives `∂g/∂xᵢ`.

The formal partial derivatives are the unique continuous derivations of the completed
polynomial algebra extending the polynomial partial derivatives; the polynomials are dense in
the completion.

## Main definitions

* `Rig.CompletedPolynomialPresentation.completedPolynomialRing`,
  `Rig.CompletedPolynomialPresentation.toAlgHom`,
  `Rig.CompletedPolynomialPresentation.extension` and
  `Rig.CompletedPolynomialPresentation.ker` — the completed polynomial algebra of a
  presentation, the presenting surjection, the associated algebra extension, and its
  kernel `J`.
* `Rig.completedPartialDeriv` — the formal partial derivative on the completed polynomial
  algebra, and `Rig.restrictedPartialDeriv` its avatar on restricted power series.
* `Rig.CompletedNaiveCotangentComplex` — the data of the complex attached to a
  presentation, and `Rig.completedNaiveCotangentComplex` its construction.
* `Rig.CompletedNaiveCotangentComplex.cochainComplex` — the realization as a cochain
  complex of `B`-modules, with the two terms lifted to a common universe.

## Main results

* `Rig.completedPartialDeriv_polynomial` — the formal partial derivatives extend the
  polynomial ones, and `Rig.denseRange_completedPolynomials` — the polynomials are dense,
  so the extension is unique.
* `Rig.CompletedNaiveCotangentComplex.degreeNegOneIso`,
  `Rig.CompletedNaiveCotangentComplex.degreeZeroIso` and
  `Rig.CompletedNaiveCotangentComplex.cochainComplex_d` — identification of the two terms
  and the differential of the cochain-complex realization.

## References

* [Stacks Project, Equation 88.3.1 (Tag 0AJR)](https://stacks.math.columbia.edu/tag/0AJR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

variable {A : Type u} [CommRing A]

namespace Rig

open AdicFiniteTypeAlgebra

namespace CompletedPolynomialPresentation

variable {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B)

/-- The completed polynomial algebra occurring in a presentation, in `P.variableCount`
variables. -/
public abbrev completedPolynomialRing := completedPolynomialAlgebra I P.variableCount

/-- The quotient map followed by the equivalence with `B`. -/
public def toAlgHom : P.completedPolynomialRing →ₐ[A] B.carrier :=
  P.quotientEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ A P.ideal)

/-- The presenting map `P.toAlgHom` is surjective. -/
public theorem toAlgHom_surjective : Function.Surjective P.toAlgHom :=
  P.quotientEquiv.surjective.comp Ideal.Quotient.mk_surjective

/-- The extension associated to the quotient presentation. Its cotangent module is `J / J²`. -/
public def extension : Algebra.Extension A B.carrier :=
  Algebra.Extension.ofSurjective P.toAlgHom P.toAlgHom_surjective

/-- The kernel `J` of a completed polynomial presentation. -/
public abbrev ker : Ideal P.completedPolynomialRing :=
  RingHom.ker P.toAlgHom.toRingHom

end CompletedPolynomialPresentation

open CompletedPolynomialPresentation

/-- The data defining the completed naive cotangent complex belonging to a fixed completed
polynomial presentation `P`. The maps `partialDeriv i` are the continuous formal partial
derivatives on the completed polynomial algebra, and `differential_mk` pins down the map
`J / J² → ⨁ i, B dxᵢ`. -/
public structure CompletedNaiveCotangentComplex {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) where
  partialDeriv : Fin P.variableCount →
    Derivation A P.completedPolynomialRing P.completedPolynomialRing
  partialDeriv_continuous : ∀ i,
    @Continuous P.completedPolynomialRing P.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount)) (partialDeriv i)
  partialDeriv_polynomial : ∀ (i : Fin P.variableCount)
      (f : MvPolynomial (Fin P.variableCount) A),
    partialDeriv i (algebraMap (MvPolynomial (Fin P.variableCount) A)
      P.completedPolynomialRing f) =
      algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing (MvPolynomial.pderiv i f)
  partialDeriv_unique : ∀ (i : Fin P.variableCount)
      (D : Derivation A P.completedPolynomialRing P.completedPolynomialRing),
    @Continuous P.completedPolynomialRing P.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount)) D →
    (∀ f : MvPolynomial (Fin P.variableCount) A,
      D (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing f) =
      algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing
          (MvPolynomial.pderiv i f)) →
    D = partialDeriv i
  differential : P.extension.Cotangent →ₗ[B.carrier] (Fin P.variableCount → B.carrier)
  differential_mk : ∀ g : P.extension.ker,
    differential (Algebra.Extension.Cotangent.mk g) =
      fun i ↦ P.toAlgHom (partialDeriv i g.1)

namespace CompletedNaiveCotangentComplex

variable {I : Ideal A} {B : AdicFiniteTypeAlgebra.{u, v} A I}
  {P : CompletedPolynomialPresentation I B}

/-- The universe-lifted copy of the conormal module `J / J²`. -/
public abbrev LiftedCotangent := ULift.{v} P.extension.Cotangent

/-- The universe-lifted free module `⨁ i, B dxᵢ`. -/
public abbrev LiftedDifferentials := ULift.{u} (Fin P.variableCount → B.carrier)

/-- The differential on the universe-lifted terms. -/
public def liftedDifferential (K : CompletedNaiveCotangentComplex P) :
    LiftedCotangent (P := P) →ₗ[B.carrier]
      LiftedDifferentials (P := P) :=
  ULift.moduleEquiv.symm.toLinearMap.comp
    (K.differential.comp ULift.moduleEquiv.toLinearMap)

/-- The lifted differential sends the lift of `x` to the lift of `K.differential x`. -/
@[simp]
public theorem liftedDifferential_up (K : CompletedNaiveCotangentComplex P)
    (x : P.extension.Cotangent) :
    K.liftedDifferential (ULift.up x) = ULift.up (K.differential x) :=
  rfl

/-- The completed naive cotangent complex as a cochain complex of `B`-modules, with `J / J²`
in degree `-1` and `⨁ i, B dxᵢ` in degree `0`. -/
public noncomputable def cochainComplex (K : CompletedNaiveCotangentComplex P) :
    CochainComplex (ModuleCat.{max u v} B.carrier) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom K.liftedDifferential)
    (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl)

/-- Identification of the degree `-1` term with the lifted conormal module `J / J²`. -/
public noncomputable def degreeNegOneIso (K : CompletedNaiveCotangentComplex P) :
    K.cochainComplex.X (-1) ≅ ModuleCat.of B.carrier (LiftedCotangent (P := P)) := by
  simpa [cochainComplex] using
    (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom K.liftedDifferential)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))

/-- Identification of the degree `0` term with the lifted free module `⨁ i, B dxᵢ`. -/
public noncomputable def degreeZeroIso (K : CompletedNaiveCotangentComplex P) :
    K.cochainComplex.X 0 ≅ ModuleCat.of B.carrier
      (LiftedDifferentials (P := P)) := by
  simpa [cochainComplex] using
    (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom K.liftedDifferential)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (by norm_num))

/-- Under the named term identifications, the differential from degree `-1` to degree `0` is
the lifted formal-derivative differential. -/
public theorem cochainComplex_d (K : CompletedNaiveCotangentComplex P) :
    K.cochainComplex.d (-1) 0 =
      K.degreeNegOneIso.hom ≫ ModuleCat.ofHom K.liftedDifferential ≫ K.degreeZeroIso.inv := by
  simpa [cochainComplex, degreeNegOneIso, degreeZeroIso] using
    (HomologicalComplex.double_d (ModuleCat.ofHom K.liftedDifferential)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl) (by norm_num))

end CompletedNaiveCotangentComplex

/-- The formal partial derivative `∂/∂xᵢ` of restricted power series, as an `A`-derivation: it is
computed coefficient quotient by coefficient quotient. -/
public noncomputable def restrictedPartialDeriv (I : Ideal A) {σ : Type*} (i : σ) :
    Derivation A (RestrictedPowerSeries I σ) (RestrictedPowerSeries I σ) := by
  let R := RestrictedPowerSeries I σ
  let d : R →ₗ[A] R := {
    toFun := partialDerivative I i
    map_add' := map_add _
    map_smul' := by
      intro a x
      apply Subtype.ext
      funext n
      change MvPolynomial.pderiv i
        (RestrictedPowerSeries.coefficientProjection I _ n (a • x)) = _
      have hx : RestrictedPowerSeries.coefficientProjection I σ n (a • x) =
          MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a) * x.val n := by
        rw [Algebra.smul_def, map_mul,
          RestrictedPowerSeries.coefficientProjection_algebraMap]
        rfl
      rw [hx]
      have hy : (RestrictedPowerSeries.coefficientProjection I σ n
          (a • partialDerivative I i x)) =
          MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a) *
            MvPolynomial.pderiv i (x.val n) := by
        rw [Algebra.smul_def, map_mul,
          RestrictedPowerSeries.coefficientProjection_algebraMap]
        rfl
      change MvPolynomial.pderiv i
        (MvPolynomial.C (Ideal.Quotient.mk (I ^ n) a) * x.val n) =
        RestrictedPowerSeries.coefficientProjection I σ n
          (a • partialDerivative I i x)
      rw [hy]
      simp
  }
  refine Derivation.mk' d ?_
  intro x y
  apply Subtype.ext
  funext n
  change MvPolynomial.pderiv i (x.val n * y.val n) =
    x.val n * MvPolynomial.pderiv i (y.val n) +
      y.val n * MvPolynomial.pderiv i (x.val n)
  rw [(MvPolynomial.pderiv i).leibniz]
  simp [smul_eq_mul]

/-- The formal partial derivative of restricted power series is formal partial differentiation of
every coefficient quotient. -/
public theorem restrictedPartialDeriv_apply (I : Ideal A) {σ : Type*} (i : σ)
    (x : RestrictedPowerSeries I σ) :
    restrictedPartialDeriv I i x = partialDerivative I i x := rfl

/-- The formal partial derivative of restricted power series is continuous for the inverse-limit
topology. -/
public theorem continuous_restrictedPartialDeriv (I : Ideal A) {σ : Type*} (i : σ) :
    @Continuous _ _ (RestrictedPowerSeries.limitTopology I σ)
      (RestrictedPowerSeries.limitTopology I σ) (restrictedPartialDeriv I i) := by
  let R := RestrictedPowerSeries I σ
  let _ : TopologicalSpace R := RestrictedPowerSeries.limitTopology I _
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⊥
  let _ : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  change Continuous (partialDerivative I i)
  refine continuous_induced_rng.mpr (continuous_pi fun n => ?_)
  change Continuous (fun f : R => MvPolynomial.pderiv i (f.val n))
  exact (continuous_of_discreteTopology :
    Continuous (MvPolynomial.pderiv i :
      MvPolynomial σ (A ⧸ I ^ n) → MvPolynomial σ (A ⧸ I ^ n))).comp
    (RestrictedPowerSeries.continuous_coefficientProjection I σ n)

/-- The formal partial derivative `∂/∂xᵢ` on the completed polynomial algebra of `P`,
corresponding to `restrictedPartialDeriv` under the equivalence with restricted power series. -/
public noncomputable def completedPartialDeriv {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    Derivation A P.completedPolynomialRing P.completedPolynomialRing := by
  let e := RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount)
  let d := restrictedPartialDeriv I i
  let L : P.completedPolynomialRing →ₗ[A] P.completedPolynomialRing :=
    e.toLinearEquiv.toLinearMap.comp
      (d.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap)
  refine Derivation.mk' L ?_
  intro x y
  change e (d (e.symm (x * y))) = x * e (d (e.symm y)) + y * e (d (e.symm x))
  rw [map_mul, Derivation.leibniz]
  simp

/-- The formal partial derivative on the completed polynomial algebra is continuous for the
inverse-limit topology. -/
public theorem continuous_completedPartialDeriv {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount) :
    @Continuous P.completedPolynomialRing P.completedPolynomialRing
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology
        I (Fin P.variableCount)) (completedPartialDeriv P i) := by
  let _ : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let h := RestrictedPowerSeries.adicCompletionHomeomorph I
    (Fin P.variableCount)
  change Continuous (fun x => h (restrictedPartialDeriv I i (h.symm x)))
  exact h.continuous_toFun.comp ((continuous_restrictedPartialDeriv I i).comp h.continuous_invFun)

/-- The polynomials are dense in the restricted power series for the inverse-limit topology. -/
public theorem denseRange_restrictedPolynomials {I : Ideal A} (σ : Type v) :
    DenseRange (RestrictedPowerSeries.polynomialAlgHom I σ) := by
  let R := RestrictedPowerSeries I σ
  let _ : TopologicalSpace R := RestrictedPowerSeries.limitTopology I σ
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⊥
  let _ : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  let T := ∀ n : ℕ, MvPolynomial σ (A ⧸ I ^ n)
  let polynomialFamily : MvPolynomial σ A → T := fun p n =>
    MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) p
  change Dense (Set.range (RestrictedPowerSeries.polynomialAlgHom I σ))
  apply (Topology.IsInducing.subtypeVal
    (t := (RestrictedPowerSeries.inverseLimitSubring I σ : Set T))).dense_iff.mpr
  intro f
  have hrange : Set.range polynomialFamily =
      Subtype.val '' Set.range (RestrictedPowerSeries.polynomialAlgHom I σ) := by
    rw [← Set.range_comp]
    rfl
  have hclose : f.val ∈ closure (Set.range polynomialFamily) := by
    apply (isTopologicalBasis_pi
      (fun _ => TopologicalSpace.isTopologicalBasis_opens)).mem_closure_iff.mpr
    intro U hU hfU
    rcases hU with ⟨g, F, hg, rfl⟩
    let N := F.sup id
    obtain ⟨p, hp⟩ := MvPolynomial.map_surjective
      (Ideal.Quotient.mk (I ^ N)) Ideal.Quotient.mk_surjective (f.val N)
    refine ⟨polynomialFamily p, ?_, ⟨p, rfl⟩⟩
    change ∀ m ∈ F, polynomialFamily p m ∈ g m
    intro m hm
    have hmN : m ≤ N := Finset.le_sup (f := id) hm
    have hcoord : MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p = f.val m := by
      calc
        MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p =
            RestrictedPowerSeries.coefficientTransition I σ hmN
              (MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p) := by
                simp [RestrictedPowerSeries.coefficientTransition,
                  RestrictedPowerSeries.idealSystemTransition,
                  MvPolynomial.map_map]
        _ = RestrictedPowerSeries.coefficientTransition I σ hmN (f.val N) := by
              rw [hp]
        _ = f.val m := f.property hmN
    change MvPolynomial.map (Ideal.Quotient.mk (I ^ m)) p ∈ g m
    rw [hcoord]
    exact hfU m hm
  rwa [hrange] at hclose

/-- The completion equivalence sends a polynomial, viewed as a restricted power series, to its
image in the completed polynomial algebra. -/
private theorem adicCompletionAlgEquiv_polynomialAlgHom {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (g : MvPolynomial (Fin P.variableCount) A) :
    RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount)
        (RestrictedPowerSeries.polynomialAlgHom I (Fin P.variableCount) g) =
      algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing g := by
  change RestrictedPowerSeries.adicCompletionEquiv I (Fin P.variableCount)
    (RestrictedPowerSeries.polynomialRingHom I (Fin P.variableCount) g) = _
  rw [RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom]
  rfl

/-- On a polynomial `f`, the formal partial derivative `completedPartialDeriv P i` is the
polynomial partial derivative `∂f/∂xᵢ`. -/
public theorem completedPartialDeriv_polynomial {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount)
    (f : MvPolynomial (Fin P.variableCount) A) :
    completedPartialDeriv P i
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing f) =
      algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
        (MvPolynomial.pderiv i f) := by
  let e := RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount)
  have heq (g : MvPolynomial (Fin P.variableCount) A) :
      e.symm (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing g) =
        RestrictedPowerSeries.polynomialAlgHom I (Fin P.variableCount) g :=
    e.symm_apply_eq.mpr (adicCompletionAlgEquiv_polynomialAlgHom P g).symm
  unfold completedPartialDeriv
  dsimp only [Derivation.coe_mk', LinearMap.coe_comp, Function.comp_apply]
  calc
    e (restrictedPartialDeriv I i
        (e.symm (algebraMap (MvPolynomial (Fin P.variableCount) A)
          P.completedPolynomialRing f))) =
        e (restrictedPartialDeriv I i
          (RestrictedPowerSeries.polynomialAlgHom I
            (Fin P.variableCount) f)) := by rw [heq f]
    _ = e (RestrictedPowerSeries.polynomialAlgHom I
          (Fin P.variableCount) (MvPolynomial.pderiv i f)) := by
      congr 1
      apply Subtype.ext
      funext n
      change MvPolynomial.pderiv i
          (MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) f) =
        MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) (MvPolynomial.pderiv i f)
      exact MvPolynomial.pderiv_map
    _ = algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing
          (MvPolynomial.pderiv i f) := adicCompletionAlgEquiv_polynomialAlgHom P _

/-- The polynomials are dense in the completed polynomial algebra for its inverse-limit
topology. -/
public theorem denseRange_completedPolynomials {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B) :
    let _ : TopologicalSpace P.completedPolynomialRing :=
      RestrictedPowerSeries.polynomialCompletionLimitTopology I
        (Fin P.variableCount);
    DenseRange (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) := by
  let _ : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let h := RestrictedPowerSeries.adicCompletionHomeomorph I
    (Fin P.variableCount)
  let p := RestrictedPowerSeries.polynomialAlgHom I (Fin P.variableCount)
  have heq : (fun f => h (p f)) =
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing) :=
    funext (adicCompletionAlgEquiv_polynomialAlgHom P)
  rw [← heq]
  exact h.surjective.denseRange.comp (denseRange_restrictedPolynomials (I := I) _)
    h.continuous_toFun

/-- The `S`-linear map `P.Cotangent → S` attached to a derivation `D` of the ring of an
algebra extension `P` of `S`: it sends the class of `g ∈ ker P` to the image of `D g` in
`S`. -/
public noncomputable def cotangentMapOfDerivation {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S) (D : Derivation R P.Ring P.Ring) :
    P.Cotangent →ₗ[S] S := by
  let f : P.ker →ₗ[P.Ring] S :=
    { toFun x := algebraMap P.Ring S (D x.1)
      map_add' := by intro x y; simp
      map_smul' := by
        intro a x
        change algebraMap P.Ring S (D (a * (x : P.Ring))) = _
        rw [Derivation.leibniz]
        have hx : algebraMap P.Ring S (x : P.Ring) = 0 := RingHom.mem_ker.mp x.2
        simp [Algebra.smul_def, hx] }
  have hf : ∀ x y : P.ker, f (x * y) = 0 := by
    intro x y
    change algebraMap P.Ring S (D ((x : P.Ring) * (y : P.Ring))) = 0
    rw [Derivation.leibniz]
    have hx : algebraMap P.Ring S (x : P.Ring) = 0 := RingHom.mem_ker.mp x.2
    have hy : algebraMap P.Ring S (y : P.Ring) = 0 := RingHom.mem_ker.mp y.2
    simp [hx, hy]
  exact ((Ideal.Cotangent.lift f hf).comp
    P.cotangentEquivCotangentKer.toLinearMap).extendScalarsOfSurjective
      P.algebraMap_surjective

/-- On the class of `g ∈ ker P`, the map attached to a derivation `D` is the image of
`D g` in `S`. -/
@[simp] public theorem cotangentMapOfDerivation_mk {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S) (D : Derivation R P.Ring P.Ring)
    (g : P.ker) :
    cotangentMapOfDerivation P D (Algebra.Extension.Cotangent.mk g) =
      algebraMap P.Ring S (D g.1) := by
  simp [cotangentMapOfDerivation, LinearMap.extendScalarsOfSurjective_apply,
    LinearMap.comp_apply, Algebra.Extension.cotangentEquivCotangentKer_apply,
    Algebra.Extension.Cotangent.val_mk, Ideal.Cotangent.lift_toCotangent]

/-- The `B`-linear map `J / J² → B` attached to a derivation `D` of the completed
polynomial algebra: it sends the class of `g ∈ J` to the image of `D g` in `B`. -/
public noncomputable def cotangentPartialDerivativeMap {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (D : Derivation A P.completedPolynomialRing P.completedPolynomialRing) :
    P.extension.Cotangent →ₗ[B.carrier] B.carrier :=
  cotangentMapOfDerivation P.extension D

/-- On the class of `g ∈ J`, the map attached to `D` is the image of `D g` under the
presenting surjection. -/
@[simp] public theorem cotangentPartialDerivativeMap_mk {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    (P : CompletedPolynomialPresentation I B)
    (D : Derivation A P.completedPolynomialRing P.completedPolynomialRing)
    (g : P.extension.ker) :
    cotangentPartialDerivativeMap P D (Algebra.Extension.Cotangent.mk g) =
      P.toAlgHom (D g.1) :=
  (cotangentMapOfDerivation_mk P.extension D g).trans rfl

/-- For a supplied presentation `B = A[x₁, …, xᵣ]̂ / J`, construct its completed naive
cotangent complex `J / J² → ⨁ i, B dxᵢ`. Its differential sends the class of a power
series `g ∈ J` to the tuple of its formal partial derivatives. -/
@[stacks 0AJR]
public noncomputable def completedNaiveCotangentComplex
    [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) : CompletedNaiveCotangentComplex P := by
  let _ : TopologicalSpace P.completedPolynomialRing :=
    RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let _ : ∀ n : ℕ, TopologicalSpace (MvPolynomial (Fin P.variableCount) (A ⧸ I ^ n)) :=
    fun _ => ⊥
  let _ : ∀ n : ℕ, DiscreteTopology
      (MvPolynomial (Fin P.variableCount) (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  let _ : TopologicalSpace (RestrictedPowerSeries I (Fin P.variableCount)) :=
    RestrictedPowerSeries.limitTopology I (Fin P.variableCount)
  let h := RestrictedPowerSeries.adicCompletionHomeomorph I
    (Fin P.variableCount)
  let _ : T2Space P.completedPolynomialRing := h.t2Space
  refine
    { partialDeriv := completedPartialDeriv P
      partialDeriv_continuous := continuous_completedPartialDeriv P
      partialDeriv_polynomial := completedPartialDeriv_polynomial P
      partialDeriv_unique := ?_
      differential := LinearMap.pi (fun i =>
        cotangentPartialDerivativeMap P (completedPartialDeriv P i))
      differential_mk := ?_ }
  · intro i D hD hpoly
    have hfun : ⇑D = ⇑(completedPartialDeriv P i) :=
      (denseRange_completedPolynomials P).equalizer hD (continuous_completedPartialDeriv P i)
        (funext fun f => (hpoly f).trans (completedPartialDeriv_polynomial P i f).symm)
    exact Derivation.ext (congrFun hfun)
  · intro g
    ext i
    exact cotangentPartialDerivativeMap_mk P (completedPartialDeriv P i) g

end Rig

end
