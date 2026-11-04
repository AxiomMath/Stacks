module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeBaseChangeRows

/-!
# The rows of the double complex of [Stacks, Tag 07LG] are quasi-isomorphic to the row zero

Let `D(•)` be the cosimplicial completed divided power envelope of a polynomial presentation
`f : A[x_i] → C` (`Crystalline.envelopeDPAlgebra s f`), `M(•)` a cosimplicial module over it,
`∇` an integrable completed connection on `M(0)`, and suppose `M(b)` is the completed base change
of `M(0)` along the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌` (`β_b : D(b) ⊗̂_{D(0)} M(0) ≅ M(b)`), so that
`M(•)` carries the cosimplicial pair `Crystalline.CosimplicialCompletedModule.baseChangePair` of
base-change connections.  This module proves the row half of the proof of
[Stacks, Proposition 60.21.3, Tag 07LG]: **every coprojection
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a quasi-isomorphism.**

The source's argument: `D(b)` is the completed divided power polynomial algebra `D(0)⟨ξ_i(j)⟩^∧`
over `D(0)` ([Stacks, Lemma 60.17.5, Tag 07L2]), the row `b` is the base change of `M(0)` to it,
and [Stacks, Lemma 60.21.2, Tag 07LD]
(`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`) says that this base
change is a quasi-isomorphism on de Rham complexes.  The base change is compared with the form
`M ⊗^∧_D Ω^*_{D'}` in which the library proves 07LD by `Crystalline.baseChangePushedEquiv`.

## The spelling of `D(0)`

[Stacks, Tag 07LD] is stated over a divided power ring `B`.  It is applied here at
`Crystalline.envelopeZeroDPRing`, the divided power ring whose carrier, ideal and divided powers
are those of the degree zero of the cosimplicial envelope, rather than at the envelope
`(tensorPowerEnvelope s f 0).object` itself: the two are equal, but only the first makes the
completed ring of `B` *reducibly* the completed ring `(envelopeDPAlgebra s f).completedRing s.p 0`
of the degree zero, which is what lets the forms, modules and connections of the cosimplicial side
be fed to 07LD without identifying instances.  The identification of [Stacks, Tag 07L2] is read
in the same spelling (`Crystalline.envelopeZeroCompletedRingEquiv`,
`Crystalline.envelopeZeroFormsEquiv`), from `Crystalline.envelopeDegreePolynomialAlgHom`.

## Main definitions and results

* `Crystalline.envelopeZeroCompletedRingEquiv`, `Crystalline.envelopeZeroFormsEquiv` —
  [Stacks, Tag 07L2] on completed rings and completed forms: `D̂(b) ≅ D̂(0)⟨ξ⟩^∧`,
  `Ω̂^a_{D(b)} ≅ Ω̂^a_{D(0)⟨ξ⟩^∧}`, carrying `σ_b` to the coefficient inclusion and the forms map
  of `σ_b` to the comparison `ψ̂` of [Stacks, Tag 07LD].
* `Crystalline.envelopeRowEquiv` — the row `b`, degree by degree, as the target of 07LD.
* `Crystalline.envelopeRowComplexIso`, `Crystalline.envelopeRowZeroComplexIso` — the row `b` and
  the row zero as the target and the source of 07LD.
* `Crystalline.quasiIso_baseChangePair_rowFromZeroHom` — **every coprojection
  `K^{*,0} ⟶ K^{*,b}` is a quasi-isomorphism.**

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Simplicial DividedPowers
open scoped TensorProduct

namespace Crystalline

section EnvelopeZero

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **The degree zero `D(0)_env` of the cosimplicial envelope, as a divided power ring**, spelled
through the cosimplicial envelope, so that its completion is literally the completed ring of the
degree zero. -/
abbrev envelopeZeroDPRing : DividedPowerRing.{u} :=
  DividedPowerRing.of ((envelopeDPAlgebra s f).carrier 0) ((envelopeDPAlgebra s f).ideal 0)
    ((envelopeDPAlgebra s f).dividedPowers 0)

/-- **[Stacks, Tag 07L2] for the degree `b`**: `D(b)_env ≅ D(0)_env⟨ξ_i(j)⟩` as `A`-algebras,
the divided power polynomial algebra taken over `Crystalline.envelopeZeroDPRing`.  It is
`Crystalline.envelopeDegreePolynomialAlgHom`. -/
def envelopeZeroPolynomialAlgHom (b : ℕ) :
    (envelopeDPAlgebra s f).carrier b →ₐ[s.A]
      setIndexedDividedPowerPolynomialAlgebra (envelopeZeroDPRing s f) (ι × Fin b) where
  toFun x := envelopeDegreePolynomialAlgHom s f b x
  map_one' := map_one (envelopeDegreePolynomialAlgHom s f b)
  map_mul' x y := map_mul (envelopeDegreePolynomialAlgHom s f b) x y
  map_zero' := map_zero (envelopeDegreePolynomialAlgHom s f b)
  map_add' x y := map_add (envelopeDegreePolynomialAlgHom s f b) x y
  commutes' r := (envelopeDegreePolynomialAlgHom s f b).commutes r

/-- The inverse of `Crystalline.envelopeZeroPolynomialAlgHom`. -/
def envelopeZeroPolynomialSymmAlgHom (b : ℕ) :
    setIndexedDividedPowerPolynomialAlgebra (envelopeZeroDPRing s f) (ι × Fin b) →ₐ[s.A]
      (envelopeDPAlgebra s f).carrier b where
  toFun y := envelopeDegreePolynomialSymmAlgHom s f b y
  map_one' := map_one (envelopeDegreePolynomialSymmAlgHom s f b)
  map_mul' x y := map_mul (envelopeDegreePolynomialSymmAlgHom s f b) x y
  map_zero' := map_zero (envelopeDegreePolynomialSymmAlgHom s f b)
  map_add' x y := map_add (envelopeDegreePolynomialSymmAlgHom s f b) x y
  commutes' r := (envelopeDegreePolynomialSymmAlgHom s f b).commutes r

/-- The identification of the degree `b` is a divided power morphism. -/
theorem envelopeZeroPolynomialAlgHom_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism ((envelopeDPAlgebra s f).dividedPowers b)
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
      (envelopeZeroPolynomialAlgHom s f b).toRingHom :=
  ⟨(envelopeDegreePolynomialAlgHom_isDPMorphism s f b).ideal_comp,
    fun a ha => (envelopeDegreePolynomialAlgHom_isDPMorphism s f b).dpow_comp a ha⟩

/-- Its inverse is a divided power morphism. -/
theorem envelopeZeroPolynomialSymmAlgHom_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
      ((envelopeDPAlgebra s f).dividedPowers b)
      (envelopeZeroPolynomialSymmAlgHom s f b).toRingHom :=
  ⟨(envelopeDegreePolynomialSymmAlgHom_isDPMorphism s f b).ideal_comp,
    fun a ha => (envelopeDegreePolynomialSymmAlgHom_isDPMorphism s f b).dpow_comp a ha⟩

/-- The inverse after the identification is the identity. -/
theorem envelopeZeroPolynomialSymmAlgHom_comp (b : ℕ) :
    AlgHom.id s.A ((envelopeDPAlgebra s f).carrier b) =
      (envelopeZeroPolynomialSymmAlgHom s f b).comp (envelopeZeroPolynomialAlgHom s f b) :=
  AlgHom.ext fun x ↦ ((envelopeDegreePolynomialEquiv s f b).symm_apply_apply x).symm

/-- The identification after the inverse is the identity. -/
theorem envelopeZeroPolynomialAlgHom_comp_symm (b : ℕ) :
    AlgHom.id s.A
        (setIndexedDividedPowerPolynomialAlgebra (envelopeZeroDPRing s f) (ι × Fin b)) =
      (envelopeZeroPolynomialAlgHom s f b).comp (envelopeZeroPolynomialSymmAlgHom s f b) :=
  AlgHom.ext fun y ↦ ((envelopeDegreePolynomialEquiv s f b).apply_symm_apply y).symm

/-- **The coefficient inclusion `D(0)_env → D(0)_env⟨ξ_i(j)⟩` is the coprojection `σ_b` followed
by the identification of the degree `b`.** -/
theorem coefficientAlgHom_eq_envelopeZeroPolynomialAlgHom_comp (b : ℕ) :
    DividedPowerPolynomial.coefficientAlgHom s.A (envelopeZeroDPRing s f) (ι × Fin b) =
      (envelopeZeroPolynomialAlgHom s f b).comp
        ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)) :=
  AlgHom.ext fun y ↦ (envelopeDegreePolynomialEquiv_map_const s f b y).symm

/-- **The completed degree `D̂(b)` is the completed divided power polynomial algebra over
`D̂(0)`**, the completion of `Crystalline.envelopeZeroPolynomialAlgHom`. -/
def envelopeZeroCompletedRingEquiv (b : ℕ) :
    (envelopeDPAlgebra s f).completedRing s.p b ≃+*
      DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
        (ι × Fin b) s.p where
  __ := adicCompletionRingMap (envelopeZeroPolynomialAlgHom s f b).toRingHom
    (map_pAdicIdeal_le s.p _)
  invFun := adicCompletionRingMap (envelopeZeroPolynomialSymmAlgHom s f b).toRingHom
    (map_pAdicIdeal_le s.p _)
  left_inv x :=
    ((adicCompletionMapₛₗ_comp_apply
      (ringHomₛₗ (envelopeZeroPolynomialAlgHom s f b).toRingHom)
      (ringHomₛₗ (envelopeZeroPolynomialSymmAlgHom s f b).toRingHom)
      (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
      (map_pAdicIdeal_le s.p _)
      (fun y ↦ ((envelopeDegreePolynomialEquiv s f b).symm_apply_apply y).symm) x).symm).trans
      (adicCompletionMapₛₗ_id_apply _ _ (fun _ ↦ rfl) x)
  right_inv x :=
    ((adicCompletionMapₛₗ_comp_apply
      (ringHomₛₗ (envelopeZeroPolynomialSymmAlgHom s f b).toRingHom)
      (ringHomₛₗ (envelopeZeroPolynomialAlgHom s f b).toRingHom)
      (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
      (map_pAdicIdeal_le s.p _)
      (fun y ↦ ((envelopeDegreePolynomialEquiv s f b).apply_symm_apply y).symm) x).symm).trans
      (adicCompletionMapₛₗ_id_apply _ _ (fun _ ↦ rfl) x)

/-- The completed identification is the completion of the uncompleted one. -/
theorem envelopeZeroCompletedRingEquiv_apply (b : ℕ)
    (x : (envelopeDPAlgebra s f).completedRing s.p b) :
    envelopeZeroCompletedRingEquiv s f b x =
      adicCompletionRingMap (envelopeZeroPolynomialAlgHom s f b).toRingHom
        (map_pAdicIdeal_le s.p _) x := rfl

/-- **The completed coprojection `σ_b : D̂(0) → D̂(b)` becomes the completed coefficient
inclusion** under `Crystalline.envelopeZeroCompletedRingEquiv`. -/
theorem envelopeZeroCompletedRingEquiv_completedRingMap_const (b : ℕ)
    (x : (envelopeDPAlgebra s f).completedRing s.p 0) :
    envelopeZeroCompletedRingEquiv s f b
        ((envelopeDPAlgebra s f).completedRingMap s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) x) =
      DividedPowerPolynomial.completedCoefficientRingHom s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p x :=
  (adicCompletionMapₛₗ_comp_apply
    (ringHomₛₗ ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)).toRingHom)
    (ringHomₛₗ (envelopeZeroPolynomialAlgHom s f b).toRingHom)
    (ringHomₛₗ (DividedPowerPolynomial.coefficientAlgHom s.A (envelopeZeroDPRing s f)
      (ι × Fin b)).toRingHom)
    (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
    (fun y ↦ (envelopeDegreePolynomialEquiv_map_const s f b y).symm) x).symm

/-- **The completed divided power de Rham complexes of `D(b)` and of `D(0)_env⟨ξ_i(j)⟩` are
isomorphic**, by `Crystalline.completedFormsDPIso` at `Crystalline.envelopeZeroPolynomialAlgHom`.
-/
def envelopeZeroFormsDPIso (b : ℕ) :
    CompletedFormsDPIso s.p s.A ((envelopeDPAlgebra s f).dividedPowers b)
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)) :=
  completedFormsDPIso s.p s.A _ _ (envelopeZeroPolynomialAlgHom s f b)
    (envelopeZeroPolynomialSymmAlgHom s f b)
    (envelopeZeroPolynomialAlgHom_isDPMorphism s f b)
    (envelopeZeroPolynomialSymmAlgHom_isDPMorphism s f b)
    (envelopeZeroPolynomialSymmAlgHom_comp s f b)
    (envelopeZeroPolynomialAlgHom_comp_symm s f b)

/-- **The forms `Ω̂^a_{D(b)}` are the completed forms of `D(0)_env⟨ξ_i(j)⟩`.** -/
def envelopeZeroFormsEquiv (b a : ℕ) :
    (envelopeDPAlgebra s f).forms s.p a b ≃+
      DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p a :=
  (envelopeZeroFormsDPIso s f b).equiv a

/-- The identification of the forms is the comparison of completed forms along the
identification of the degree `b`. -/
theorem envelopeZeroFormsEquiv_apply (b a : ℕ) (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeZeroFormsEquiv s f b a x =
      completedMapDifferentialForms s.p s.A ((envelopeDPAlgebra s f).dividedPowers b)
        (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
        (envelopeZeroPolynomialAlgHom s f b)
        (envelopeZeroPolynomialAlgHom_isDPMorphism s f b) a x := by
  unfold envelopeZeroFormsEquiv envelopeZeroFormsDPIso
  exact completedFormsDPIso_equiv_apply _ _ _ _ _ _ _ _ _ _ _ _

/-- Its inverse is the comparison along the inverse identification. -/
theorem envelopeZeroFormsEquiv_symm_apply (b a : ℕ)
    (y : DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
      (ι × Fin b) s.p a) :
    (envelopeZeroFormsEquiv s f b a).symm y =
      completedMapDifferentialForms s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
        ((envelopeDPAlgebra s f).dividedPowers b)
        (envelopeZeroPolynomialSymmAlgHom s f b)
        (envelopeZeroPolynomialSymmAlgHom_isDPMorphism s f b) a y := by
  unfold envelopeZeroFormsEquiv envelopeZeroFormsDPIso
  exact completedFormsDPIso_equiv_symm_apply _ _ _ _ _ _ _ _ _ _ _ _

/-- The identification of the forms is semilinear over the identification of the rings. -/
theorem envelopeZeroFormsEquiv_smul (b a : ℕ) (r : (envelopeDPAlgebra s f).completedRing s.p b)
    (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeZeroFormsEquiv s f b a (r • x) =
      envelopeZeroCompletedRingEquiv s f b r • envelopeZeroFormsEquiv s f b a x :=
  (envelopeZeroFormsEquiv_apply s f b a (r • x)).trans
    ((adicCompletionMapₛₗ_smul _ _ r x).trans
      (congrArg (envelopeZeroCompletedRingEquiv s f b r • ·)
        (envelopeZeroFormsEquiv_apply s f b a x).symm))

/-- Its inverse is semilinear over the inverse identification of the rings. -/
theorem envelopeZeroFormsEquiv_symm_smul (b a : ℕ)
    (r : DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
      (ι × Fin b) s.p)
    (y : DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
      (ι × Fin b) s.p a) :
    (envelopeZeroFormsEquiv s f b a).symm (r • y) =
      (envelopeZeroCompletedRingEquiv s f b).symm r • (envelopeZeroFormsEquiv s f b a).symm y :=
  (envelopeZeroFormsEquiv s f b a).injective <| by
    rw [envelopeZeroFormsEquiv_smul]; simp

/-- `Crystalline.envelopeZeroFormsEquiv` as a semilinear map. -/
def envelopeZeroFormsMapₛₗ (b a : ℕ) :
    (envelopeDPAlgebra s f).forms s.p a b →ₛₗ[(envelopeZeroCompletedRingEquiv s f b :
      (envelopeDPAlgebra s f).completedRing s.p b →+*
        DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
          (ι × Fin b) s.p)]
      DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p a where
  toFun := envelopeZeroFormsEquiv s f b a
  map_add' := map_add _
  map_smul' := envelopeZeroFormsEquiv_smul s f b a

/-- Its inverse, as a semilinear map. -/
def envelopeZeroFormsInvₛₗ (b a : ℕ) :
    DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p a →ₛₗ[((envelopeZeroCompletedRingEquiv s f b).symm :
      DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
          (ι × Fin b) s.p →+* (envelopeDPAlgebra s f).completedRing s.p b)]
      (envelopeDPAlgebra s f).forms s.p a b where
  toFun := (envelopeZeroFormsEquiv s f b a).symm
  map_add' := map_add _
  map_smul' r y := envelopeZeroFormsEquiv_symm_smul s f b a r y

/-- The identification of the forms respects the universal differentials. -/
theorem envelopeZeroFormsEquiv_differential (b : ℕ)
    (r : (envelopeDPAlgebra s f).completedRing s.p b) :
    envelopeZeroFormsEquiv s f b 1 ((envelopeDPAlgebra s f).differential s.p b r) =
      completedFormsDifferential s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
        (envelopeZeroCompletedRingEquiv s f b r) := by
  refine (envelopeZeroFormsEquiv_apply s f b 1 _).trans ?_
  rw [envelopeZeroCompletedRingEquiv_apply]
  exact completedMapDifferentialForms_completedFormsDifferential s.p s.A
    ((envelopeDPAlgebra s f).dividedPowers b)
    (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
    (envelopeZeroPolynomialAlgHom s f b) (envelopeZeroPolynomialAlgHom_isDPMorphism s f b) r

/-- **The transition of the forms along `σ_b` is the comparison `ψ̂` of
[Stacks, Lemma 60.21.2, Tag 07LD]** under `Crystalline.envelopeZeroFormsEquiv`. -/
theorem envelopeZeroFormsEquiv_formsMapCompleted_const (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a 0) :
    envelopeZeroFormsEquiv s f b a
        ((envelopeDPAlgebra s f).formsMapCompleted s.p (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a x) =
      DividedPowerPolynomial.completedFormsComparison s.A (envelopeZeroDPRing s f) (ι × Fin b)
        s.p a x := by
  let : LinearOrder (ι × Fin b) := IsWellOrder.linearOrder WellOrderingRel
  refine (envelopeZeroFormsEquiv_apply s f b a _).trans ?_
  refine ((completedMapDifferentialForms_eq_comp s.p s.A
    ((envelopeDPAlgebra s f).dividedPowers 0) ((envelopeDPAlgebra s f).dividedPowers b)
    (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b))
    ((envelopeDPAlgebra s f).map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (envelopeZeroPolynomialAlgHom s f b)
    (DividedPowerPolynomial.coefficientAlgHom s.A (envelopeZeroDPRing s f) (ι × Fin b))
    ((envelopeDPAlgebra s f).map_isDPMorphism (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (envelopeZeroPolynomialAlgHom_isDPMorphism s f b)
    (DividedPowerPolynomial.coefficientAlgHom_isDPMorphism s.A (envelopeZeroDPRing s f)
      (ι × Fin b))
    (coefficientAlgHom_eq_envelopeZeroPolynomialAlgHom_comp s f b) a x).symm).trans ?_
  exact (DividedPowerPolynomial.completedCoefficientFormsMapₗ_apply s.A
    (envelopeZeroDPRing s f) (ι × Fin b) s.p a x).symm

/-- The identification of the forms respects the wedge products. -/
theorem envelopeZeroFormsEquiv_wedge (b a : ℕ)
    (x : (envelopeDPAlgebra s f).forms s.p a b) (y : (envelopeDPAlgebra s f).forms s.p 1 b) :
    envelopeZeroFormsEquiv s f b (a + 1) ((envelopeDPAlgebra s f).wedge s.p b a x y) =
      completedDividedPowerWedge s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)) a
        (envelopeZeroFormsEquiv s f b a x) (envelopeZeroFormsEquiv s f b 1 y) :=
  (envelopeZeroFormsDPIso s f b).wedge a x y

/-- The identification of the forms respects the de Rham differentials. -/
theorem envelopeZeroFormsEquiv_deRham (b a : ℕ) (x : (envelopeDPAlgebra s f).forms s.p a b) :
    envelopeZeroFormsEquiv s f b (a + 1) ((envelopeDPAlgebra s f).deRham s.p b a x) =
      completedDividedPowerDeRham s.p s.A
        (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)) a
        (envelopeZeroFormsEquiv s f b a x) :=
  (envelopeZeroFormsDPIso s f b).deRham a x

end EnvelopeZero

section EnvelopeRows

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The completed ring `D(0)` of the degree zero, spelled as the completed divided power ring of
`Crystalline.envelopeZeroDPRing`; it is `(envelopeDPAlgebra s f).completedRing s.p 0`. -/
abbrev envelopeZeroRing : Type u :=
  completedDividedPowerRing s.p (B := (envelopeZeroDPRing s f : Type u))

/-- The forms of `D(0)⟨ξ⟩^∧` as a `D(0)`-module, the action of [Stacks, Tag 07LD]
(`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`).  It is declared here
because instance search does not see `D(0)` as the completed ring of a divided power ring. -/
instance envelopeRowFormsModule (b i : ℕ) :
    Module (envelopeZeroRing s f)
      (DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p i) :=
  DividedPowerPolynomial.moduleCompletedPolynomialForms s.A (envelopeZeroDPRing s f)
    (ι × Fin b) s.p i

/-- **`D(0)⟨ξ⟩^∧` as a `D(0)`-algebra** along the completed coefficient inclusion. -/
abbrev envelopeRowAlgebra (b : ℕ) :
    Algebra (envelopeZeroRing s f)
      (DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
        (ι × Fin b) s.p) :=
  (DividedPowerPolynomial.completedCoefficientRingHom s.A (envelopeZeroDPRing s f)
    (ι × Fin b) s.p).toAlgebra

/-- The `D(0)`-action on the forms of `D(0)⟨ξ⟩^∧` is the action through the coefficient
inclusion. -/
theorem envelopeRow_isScalarTower (b i : ℕ) :
    letI := envelopeRowAlgebra s f b
    IsScalarTower (envelopeZeroRing s f)
      (DividedPowerPolynomial.completedDividedPowerPolynomialRing (envelopeZeroDPRing s f)
        (ι × Fin b) s.p)
      (DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p i) :=
  let := envelopeRowAlgebra s f b
  ⟨fun x y z => mul_smul (DividedPowerPolynomial.completedCoefficientRingHom s.A
    (envelopeZeroDPRing s f) (ι × Fin b) s.p x) y z⟩

variable (V : CosimplicialCompletedModule.{u, u, u} (envelopeDPAlgebra s f) s.p)
  (beta : ∀ b : ℕ, letI := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
    CompletedConnection.baseChangeCarrier s.p ((envelopeDPAlgebra s f).completedRing s.p 0)
      ((envelopeDPAlgebra s f).completedRing s.p b) (V.carrier 0)
        ≃ₗ[(envelopeDPAlgebra s f).completedRing s.p b] V.carrier b)

/-- **The row `b` of the double complex, identified with the target of
[Stacks, Lemma 60.21.2, Tag 07LD]**, degree by degree. -/
def envelopeRowEquiv (b i : ℕ) :
    CompletedTensor s.p ((envelopeDPAlgebra s f).completedRing s.p b)
        ((envelopeDPAlgebra s f).forms s.p i b) (V.carrier b) ≃+
      CompletedTensor s.p (envelopeZeroRing s f)
        (DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
          (ι × Fin b) s.p i) (V.carrier 0) :=
  letI := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
  letI := envelopeRowAlgebra s f b
  haveI := envelopeRow_isScalarTower s f b
  baseChangePushedEquiv s.p (envelopeZeroCompletedRingEquiv s f b)
    (fun c => envelopeZeroCompletedRingEquiv_completedRingMap_const s f b c) (V.carrier 0)
    (fun a => (envelopeDPAlgebra s f).forms s.p a b)
    (DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (envelopeZeroFormsMapₛₗ s f b) (envelopeZeroFormsInvₛₗ s f b)
    (fun j ω => (envelopeZeroFormsEquiv s f b j).symm_apply_apply ω)
    (fun j ω => (envelopeZeroFormsEquiv s f b j).apply_symm_apply ω) (V.carrier b) (beta b) i

/-- The identification of the forms carries the transition of the coprojection to the
comparison `ψ̂` of [Stacks, Lemma 60.21.2, Tag 07LD]. -/
theorem envelopeZeroFormsMapₛₗ_coprojectionFormsMap (b i : ℕ)
    (ω : (envelopeDPAlgebra s f).forms s.p i 0) :
    letI := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
    envelopeZeroFormsMapₛₗ s f b i ((envelopeDPAlgebra s f).coprojectionFormsMap s.p b i ω) =
      DividedPowerPolynomial.completedFormsComparison s.A (envelopeZeroDPRing s f) (ι × Fin b)
        s.p i ω :=
  envelopeZeroFormsEquiv_formsMapCompleted_const s f b i ω

variable (hbeta : ∀ (b : ℕ) (x : (envelopeDPAlgebra s f).completedRing s.p b) (m : V.carrier 0),
    letI := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
    beta b (AdicCompletion.of (pAdicIdeal (A := (envelopeDPAlgebra s f).completedRing s.p b) s.p)
        ((envelopeDPAlgebra s f).completedRing s.p b ⊗[(envelopeDPAlgebra s f).completedRing s.p 0]
          V.carrier 0) (x ⊗ₜ[(envelopeDPAlgebra s f).completedRing s.p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

include hbeta in
/-- **The identification of the row `b` carries the coprojection `K^{*,0} ⟶ K^{*,b}` to the
comparison `1 ⊗ ψ̂` of [Stacks, Lemma 60.21.2, Tag 07LD].** -/
theorem envelopeRowEquiv_tensorMap (b i : ℕ) (z : V.obj i 0) :
    envelopeRowEquiv s f V beta b i (V.tensorMap (CosimplicialDPAlgebra.coprojection b) i z) =
      DividedPowerPolynomial.completedModuleComparison s.A (envelopeZeroDPRing s f) (ι × Fin b)
        s.p (V.carrier 0) i z :=
  let := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
  let := envelopeRowAlgebra s f b
  have := envelopeRow_isScalarTower s f b
  (congrArg (envelopeRowEquiv s f V beta b i)
    (V.tensorMap_eq_comparisonValues (CosimplicialDPAlgebra.coprojection b) i z)).trans <|
  baseChangePushedEquiv_comparisonValues s.p (envelopeZeroCompletedRingEquiv s f b)
    (fun c => envelopeZeroCompletedRingEquiv_completedRingMap_const s f b c) (V.carrier 0)
    (fun a => (envelopeDPAlgebra s f).forms s.p a 0)
    (fun a => (envelopeDPAlgebra s f).forms s.p a b)
    (DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (fun a => (envelopeDPAlgebra s f).coprojectionFormsMap s.p b a)
    (fun a => DividedPowerPolynomial.completedFormsComparison s.A (envelopeZeroDPRing s f)
      (ι × Fin b) s.p a)
    (envelopeZeroFormsMapₛₗ s f b) (envelopeZeroFormsInvₛₗ s f b)
    (fun j ω => (envelopeZeroFormsEquiv s f b j).symm_apply_apply ω)
    (fun j ω => (envelopeZeroFormsEquiv s f b j).apply_symm_apply ω)
    (envelopeZeroFormsMapₛₗ_coprojectionFormsMap s f b) (V.carrier b) (beta b)
    (V.map (CosimplicialDPAlgebra.coprojection b))
    (fun m => by rw [CompletedConnection.baseChangeInclusion_apply, hbeta, one_smul]) i z

variable (nabla : CompletedConnection s.p ((envelopeDPAlgebra s f).completedRing s.p 0)
    ((envelopeDPAlgebra s f).forms s.p 1 0) ((envelopeDPAlgebra s f).differential s.p 0)
    (V.carrier 0))

include hbeta in
/-- **The identification of the row `b` commutes with the de Rham differentials**: that of
`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` for the base-change connection, and that of
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)⟨ξ⟩^∧}` for `∇` pushed into the forms of `D(0)⟨ξ⟩^∧`. -/
theorem envelopeRowEquiv_differential (b i : ℕ)
    (x : CompletedTensor s.p ((envelopeDPAlgebra s f).completedRing s.p b)
      ((envelopeDPAlgebra s f).forms s.p i b) (V.carrier b)) :
    envelopeRowEquiv s f V beta b (i + 1)
        (CompletedDeRham.differential s.p ((envelopeDPAlgebra s f).completedRing s.p b)
          (fun a => (envelopeDPAlgebra s f).forms s.p a b) ((envelopeDPAlgebra s f).wedge s.p b)
          ((envelopeDPAlgebra s f).deRham s.p b) (V.carrier b) (V.baseChangeConnection nabla beta b)
          ((envelopeDPAlgebra s f).isGradedLeibniz s.p b) i x) =
      DividedPowerPolynomial.completedTargetDifferential s.A (envelopeZeroDPRing s f) (ι × Fin b)
        s.p (V.carrier 0) nabla i (envelopeRowEquiv s f V beta b i x) :=
  let := (envelopeDPAlgebra s f).coprojectionAlgebra s.p b
  let := envelopeRowAlgebra s f b
  have := envelopeRow_isScalarTower s f b
  baseChangePushedEquiv_differential (p := s.p) (u := envelopeZeroCompletedRingEquiv s f b)
    (hu := fun c => envelopeZeroCompletedRingEquiv_completedRingMap_const s f b c)
    (M := V.carrier 0) (Om := fun a => (envelopeDPAlgebra s f).forms s.p a 0)
    (OmB := fun a => (envelopeDPAlgebra s f).forms s.p a b)
    (Om' := DividedPowerPolynomial.completedPolynomialForms s.A (envelopeZeroDPRing s f)
      (ι × Fin b) s.p)
    (dB := (envelopeDPAlgebra s f).differential s.p b)
    (d' := completedFormsDifferential s.p s.A
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)))
    (dD := DividedPowerPolynomial.completedPolynomialFormsDifferential s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (nabla := nabla)
    (psiB := fun a => (envelopeDPAlgebra s f).coprojectionFormsMap s.p b a)
    (psi := fun a => DividedPowerPolynomial.completedFormsComparison s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p a)
    (fB := envelopeZeroFormsMapₛₗ s f b) (fBinv := envelopeZeroFormsInvₛₗ s f b)
    (hfB := fun j ω => (envelopeZeroFormsEquiv s f b j).symm_apply_apply ω)
    (hfB' := fun j ω => (envelopeZeroFormsEquiv s f b j).apply_symm_apply ω)
    (hfpsi := envelopeZeroFormsMapₛₗ_coprojectionFormsMap s f b)
    (hfd := envelopeZeroFormsEquiv_differential s f b)
    (hdBadd := (envelopeDPAlgebra s f).differential_add s.p b)
    (hdBleib := (envelopeDPAlgebra s f).differential_mul s.p b)
    (hpsiB1 := (envelopeDPAlgebra s f).coprojectionFormsMap_differential s.p b)
    (hd'add := completedFormsDifferential_add s.p s.A _)
    (hd'leib := completedFormsDifferential_mul s.p s.A _)
    (hpsi1 := DividedPowerPolynomial.completedFormsComparison_completedFormsDifferential s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (MB := V.carrier b) (β := beta b)
    (wedgeB := (envelopeDPAlgebra s f).wedge s.p b)
    (deRhamB := (envelopeDPAlgebra s f).deRham s.p b)
    (hleibB := (envelopeDPAlgebra s f).isGradedLeibniz s.p b)
    (wedge' := completedDividedPowerWedge s.p s.A
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)))
    (deRham' := completedDividedPowerDeRham s.p s.A
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeZeroDPRing s f) (ι × Fin b)))
    (hleib' := isGradedLeibniz_completedDividedPower s.p s.A _)
    (hfwedge := envelopeZeroFormsEquiv_wedge s f b)
    (hfdeRham := envelopeZeroFormsEquiv_deRham s f b)
    (wedgeD := DividedPowerPolynomial.completedPolynomialFormsWedge s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (hwedgeD := fun _ _ _ => rfl)
    (hleibD := DividedPowerPolynomial.completedPolynomialForms_isGradedLeibniz s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p)
    (nablaD := DividedPowerPolynomial.completedPushedConnection s.A
      (envelopeZeroDPRing s f) (ι × Fin b) s.p (V.carrier 0) nabla)
    (hnablaD := fun _ => rfl)
    (nablaB := V.baseChangeConnection nabla beta b)
    (hnablaB := fun y => V.baseChangeConnection_apply nabla beta b y) i x

variable (hδ : ∀ x : V.carrier 0,
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
  (hint : CompletedDeRham.HasIntegrableConnection s.p
    ((envelopeDPAlgebra s f).completedRing s.p 0) (fun a => (envelopeDPAlgebra s f).forms s.p a 0)
    ((envelopeDPAlgebra s f).wedge s.p 0) ((envelopeDPAlgebra s f).deRham s.p 0) (V.carrier 0)
    nabla ((envelopeDPAlgebra s f).isGradedLeibniz s.p 0))

include hbeta in
/-- **The row `b` of the double complex is isomorphic to the target of
[Stacks, Lemma 60.21.2, Tag 07LD]**, as a complex. -/
def envelopeRowComplexIso (b : ℕ) :
    (V.baseChangePair nabla beta hbeta hδ hint).degreeDeRhamComplex b ≅
      DividedPowerPolynomial.completedTargetDeRhamComplex s.A (envelopeZeroDPRing s f)
        (ι × Fin b) s.p (V.carrier 0) nabla hint :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (envelopeRowEquiv s f V beta b i).toAddCommGrpIso)
    (fun i j hij => by
      change i + 1 = j at hij
      subst hij
      rw [CosimplicialCompletedPair.degreeDeRhamComplex_d,
        DividedPowerPolynomial.completedTargetDeRhamComplex_d s.A (envelopeZeroDPRing s f)
          (ι × Fin b) s.p (V.carrier 0) nabla hint i]
      exact AddCommGrpCat.ext fun x =>
        (envelopeRowEquiv_differential s f V beta hbeta nabla b i x).symm)

include hbeta in
/-- **The row zero of the double complex is the source of [Stacks, Lemma 60.21.2, Tag 07LD]**:
the connection of degree zero is `∇` itself. -/
def envelopeRowZeroComplexIso :
    (V.baseChangePair nabla beta hbeta hδ hint).degreeDeRhamComplex 0 ≅
      DividedPowerPolynomial.completedSourceDeRhamComplex s.A (envelopeZeroDPRing s f) s.p
        (V.carrier 0) nabla hint :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j hij => by
      change i + 1 = j at hij
      subst hij
      have h : V.baseChangeConnection nabla beta 0 = nabla :=
        CompletedConnection.ext fun y => V.baseChangeConnection_zero nabla beta hbeta y
      rw [CosimplicialCompletedPair.degreeDeRhamComplex_d,
        DividedPowerPolynomial.completedSourceDeRhamComplex_d s.A (envelopeZeroDPRing s f) s.p
          (V.carrier 0) nabla hint i]
      refine AddCommGrpCat.ext fun x => ?_
      change CompletedDeRham.differential s.p _ _ _ _ _ nabla _ i x =
        CompletedDeRham.differential s.p _ _ _ _ _ (V.baseChangeConnection nabla beta 0) _ i x
      rw [h]
      rfl)

include hbeta in
/-- **Every coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of the double
complex is a quasi-isomorphism**: read through `Crystalline.envelopeRowZeroComplexIso` and
`Crystalline.envelopeRowComplexIso` it is the comparison of [Stacks, Lemma 60.21.2, Tag 07LD],
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`, for the presentation of
`D(b)` as a completed divided power polynomial algebra over `D(0)` of
[Stacks, Lemma 60.17.5, Tag 07L2]. -/
theorem quasiIso_baseChangePair_rowFromZeroHom (b : ℕ) :
    QuasiIso ((V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b) := by
  have hsq : (V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b ≫
      (envelopeRowComplexIso s f V beta hbeta nabla hδ hint b).hom =
        (envelopeRowZeroComplexIso s f V beta hbeta nabla hδ hint).hom ≫
          DividedPowerPolynomial.completedDeRhamComparison s.A (envelopeZeroDPRing s f)
            (ι × Fin b) s.p (V.carrier 0) nabla hint := by
    refine HomologicalComplex.hom_ext _ _ fun i => AddCommGrpCat.ext fun z => ?_
    exact envelopeRowEquiv_tensorMap s f V beta hbeta b i z
  have := DividedPowerPolynomial.quasiIso_completedDeRhamComparison s.A
    (envelopeZeroDPRing s f) (ι × Fin b) s.p (V.carrier 0) nabla hint
  have h2 : QuasiIso ((V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b ≫
      (envelopeRowComplexIso s f V beta hbeta nabla hδ hint b).hom) := by
    rw [hsq]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp h2

end EnvelopeRows

end Crystalline
