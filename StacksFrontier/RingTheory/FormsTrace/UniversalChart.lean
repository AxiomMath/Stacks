module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalPointed
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierMapPushout
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors
public import StacksFrontier.RingTheory.FormsTrace.UniversalNice
public import StacksFrontier.RingTheory.Smooth.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal nice charts for finite syntomic algebras

Let `A_d` be the universal ring of structure constants of free commutative algebras of rank `d`
whose first basis vector is the unit (Tag 05YM), let `X_d = Spec(A_d)`, and let `U_d ⊆ X_d` be
the open subscheme over which the universal finite free family is syntomic (Tag 0FL0). For a
ring map `c : A_d → R` write `B_c` for the algebra `Carrier (tableOfHom c)`, free over `R` on the
basis `Carrier.basis`, whose structure constants are the images of the universal ones: it is the
base change of the universal family along `c`.

This file builds the universal charts on which the trace on forms of Stacks, Lemma 0FLB and
Proposition 0FLC is unique.

* **The bridge.** `B_c` is syntomic (resp. étale) over `R` exactly when the morphism
  `Spec(R) → X_d` defined by `c` lands in `U_d` (resp. in the étale locus `U'_d` of Tag 0FL2).
* **Good elements.** An element `g ∈ A_d` is *syntomic-good* if the principal open `D(g)` lies
  in `U_d`. Put `N_g = A_d[1/g]`. Then `N_g` is smooth over `ℤ` (Tag 0FL1), hence reduced, and
  Noetherian.
* **The charts.** For any type `σ` of variables put `R = N_g[x_σ]` and let `B_R` be the base
  change of the universal family to `R`, with its basis `e`. Then `R` is formally smooth over `ℤ`
  (so `Ω_{R/ℤ}` is projective), and smooth and Noetherian when `σ` is finite; `B_R` is syntomic,
  finite and free over `R`; and the discriminant `Δ = disc_{B_R/R}(e)` is a nonzerodivisor of
  `R`, because the étale locus is dense in `U_d` (Tag 0FL2), so that the principal open of `Δ`
  is dense in `Spec(N_g)`, `N_g` is reduced, and `N_g → R` is flat. Consequently `Δ` is a nice
  element (`Stacks.FormsTrace.IsNiceElement`), by `Stacks.FormsTrace.discr_nice`.

## Main definitions

* `Stacks.FormsTrace.universalCarrierLift`: the comparison map from the universal carrier `B_d`
  to `B_c`.
* `Stacks.FormsTrace.universalDiscr`: the universal discriminant.
* `Stacks.FormsTrace.IsSyntomicGood`: `D(g) ⊆ U_d`.
* `Stacks.FormsTrace.universalChartBase`: the ring `N_g = A_d[1/g]`, in the universe of the final
  rings, and `Stacks.FormsTrace.universalChartBaseClassify`: the map `A_d → N_g`.
* `Stacks.FormsTrace.polynomialChart`: the polynomial ring `R[x_σ]` over a ring `R`.
* `Stacks.FormsTrace.universalChartRing`, `Stacks.FormsTrace.universalChartClassify`:
  `R = N_g[x_σ]` and the map `A_d → R`.

## Main results

* `Stacks.FormsTrace.isPushout_universalCarrier`: `B_c` is the base change of `B_d` along `c`.
* `Stacks.FormsTrace.syntomic_tableOfHom_iff`, `Stacks.FormsTrace.etale_tableOfHom_iff`: the
  bridge.
* `Stacks.FormsTrace.discr_tableOfHom`: the discriminant of `B_c` is `c` of the universal one.
* `Stacks.FormsTrace.isSyntomicGood_iff`: `g` is good exactly when `B` is syntomic over `N_g`.
* `Stacks.FormsTrace.syntomic_tableOfHom_of_isUnit`: if `g` is good and `c g` is a unit, `B_c`
  is syntomic.
* `Stacks.FormsTrace.smooth_universalChartBase`, `Stacks.FormsTrace.isReduced_universalChartBase`,
  `Stacks.FormsTrace.isNoetherianRing_universalChartBase`.
* `Stacks.FormsTrace.discr_universalChartBase_mem_nonZeroDivisors`: the discriminant over `N_g` is
  a nonzerodivisor.
* `Stacks.FormsTrace.discr_polynomialChart_nice`: nice elements on polynomial charts.
* `Stacks.FormsTrace.universalChartRing_formallySmooth`,
  `Stacks.FormsTrace.universalChartRing_projective_kaehler`,
  `Stacks.FormsTrace.universalChartRing_smooth`,
  `Stacks.FormsTrace.universalChartRing_isNoetherianRing`,
  `Stacks.FormsTrace.universalChartRing_syntomic`,
  `Stacks.FormsTrace.discr_universalChartRing_mem_nonZeroDivisors` and
  `Stacks.FormsTrace.discr_universalChartRing_nice`: the properties of the charts.

## Implementation notes

The base change square `A_d → B_d`, `A_d → R`, `B_d → B_c`, `R → B_c` is a pushout of rings by
`AlgebraicGeometry.isPushout_of_bases_one`, both horizontal maps being free on the distinguished
bases; `Spec` turns it into the cartesian square identifying `B_c` with the global sections of
the base change of the universal family, and `AlgebraicGeometry.HasRingHomProperty.Spec_iff`
translates syntomicity and étaleness of that base change into the corresponding property of
`R → B_c`. Everything lives in one universe `u`: the universal ring is lifted to
`ULift.{u} A_d`, as it is to form `X_d`, so `N_g` is the localization of the lifted ring.

The rings `N_g` and `R[x_σ]` are type synonyms (`def`s) carrying only their ring and algebra
structures. On `Localization.Away` and `MvPolynomial` instance search finds a `ℤ`-algebra
structure which is not definitionally `Ring.toIntAlgebra`, the one generic statements about
`Ω[A⁄ℤ]` and `KaehlerDifferential.mapBaseChange ℤ A B` see; on the synonyms only the canonical
one exists.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FL1](https://stacks.math.columbia.edu/tag/0FL1)
* [Stacks Project, Tag 0FL2](https://stacks.math.columbia.edu/tag/0FL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section Bridge

variable {R : Type u} [CommRing R]

/-- The comparison map from the (lifted) universal carrier `B_d` to the algebra `B_c` of the
table of a ring map `c : A_d → R`: coordinatewise application of `c`. -/
def universalCarrierLift (c : universalRing d →+* R) :
    letI := (universalAlgebraStructure d).ring
    ULift.{u} (UniversalFiniteFreeModule d) →+* Carrier (tableOfHom c) :=
  letI := (universalAlgebraStructure d).ring
  (universalCarrierClassify d (universalAlgebraStructure d) (tableOfHom c)).comp
    ULift.ringEquiv.toRingHom

/-- **The algebra of the table of `c` is the base change of the universal carrier along `c`.**
The square formed by `A_d → B_d`, `c : A_d → R`, the comparison map `B_d → B_c` and
`R → B_c` is a pushout of commutative rings. -/
theorem isPushout_universalCarrier (c : universalRing d →+* R) :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    IsPushout (CommRingCat.ofHom (RingHom.ulift
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d))))
      (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
        ULift.{u} (universalRing d) →+* universalRing d)))
      (CommRingCat.ofHom (universalCarrierLift c))
      (CommRingCat.ofHom (algebraMap R (Carrier (tableOfHom c)))) := by
  classical
  let s := universalAlgebraStructure d
  let := s.ring
  let := s.algebra
  let : Algebra (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule d)) :=
    (RingHom.ulift (algebraMap (universalRing d) (UniversalFiniteFreeModule d))).toAlgebra
  let : Module (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule d)) :=
    Algebra.toModule
  let : SMul (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule d)) :=
    Algebra.toSMul
  let : Algebra (ULift.{u} (universalRing d)) R := (c.comp ULift.ringEquiv.toRingHom).toAlgebra
  let : Algebra (ULift.{u} (UniversalFiniteFreeModule d)) (Carrier (tableOfHom c)) :=
      (universalCarrierLift c).toAlgebra
  let : Algebra (ULift.{u} (universalRing d)) (Carrier (tableOfHom c)) := ((algebraMap R (Carrier
      (tableOfHom c))).comp (algebraMap (ULift.{u} (universalRing d)) R)).toAlgebra
  have : IsScalarTower (ULift.{u} (universalRing d)) R (Carrier (tableOfHom c)) :=
      IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq (R := ULift.{u} (universalRing d))
    (S := ULift.{u} (UniversalFiniteFreeModule d)) (A := Carrier (tableOfHom c)) fun a => by
    change algebraMap R (Carrier (tableOfHom c)) (c a.down) =
      universalCarrierClassify d s (tableOfHom c) (algebraMap _ _ a.down)
    rw [universalCarrierClassify_algebraMap, classify_tableOfHom]
  have hsmul : ∀ (a : (ULift.{u} (universalRing d))) (x : (ULift.{u} (UniversalFiniteFreeModule
      d))) (i : Fin d),
      (a • x).down.coeff i = a.down * x.down.coeff i := by
    intro a x i
    have h := congrFun ((universalCarrierLinearEquiv d).map_smul a.down x.down) i
    rwa [Algebra.smul_def] at h
  let eS : (ULift.{u} (UniversalFiniteFreeModule d)) ≃ₗ[(ULift.{u} (universalRing d))] (Fin d →
      (ULift.{u} (universalRing d))) :=
    { toFun := fun x i => ULift.up (x.down.coeff i)
      invFun := fun y => ULift.up ⟨fun i => (y i).down⟩
      map_add' := fun x y => funext fun i => by
        change ULift.up ((x.down + y.down).coeff i) = _
        rw [s.add_coeff]
        rfl
      map_smul' := fun a x => funext fun i => by
        change ULift.up ((a • x).down.coeff i) = ULift.up (a.down * x.down.coeff i)
        rw [hsmul]
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let bU : Module.Basis (Fin d) (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule
      d)) := Module.Basis.ofEquivFun eS
  have : Algebra.IsPushout (ULift.{u} (universalRing d)) (ULift.{u} (UniversalFiniteFreeModule d))
      R (Carrier (tableOfHom c)) := by
    refine isPushout_of_bases_one bU (Carrier.basis (tableOfHom c)) fun x => ?_
    refine Carrier.ext fun k => ?_
    change (tableOfHom c).classify (x.down.coeff k) = _
    rw [classify_tableOfHom, Carrier.sum_apply (s := Finset.univ)]
    have hterm : ∀ i : Fin d,
        (algebraMap (ULift.{u} (universalRing d)) R (bU.repr x i) • Carrier.basis (tableOfHom c) i)
            k =
          c (x.down.coeff i) * (if k = i then 1 else 0) := by
      intro i
      rw [Carrier.smul_apply, Carrier.basis_apply, Carrier.basisVector_apply,
        Module.Basis.ofEquivFun_repr_apply]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi])
        (absurd (Finset.mem_univ k))]
    simp
  exact CommRingCat.isPushout_of_isPushout (ULift.{u} (universalRing d)) (ULift.{u}
      (UniversalFiniteFreeModule d)) R (Carrier (tableOfHom c))

/-- **The base change of the universal family along `c`, read on rings.** For a property `P` of
morphisms of schemes given affine-locally by a property `Q` of ring maps, the base change of the
universal family along `Spec(R) → X_d` has `P` exactly when `R → B_c` has `Q`. -/
theorem universalFamily_pullback_snd_iff (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    (c : universalRing d →+* R) :
    P (pullback.snd (universalFamily.{u} d (universalAlgebraStructure d))
      (Spec.map (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
        ULift.{u} (universalRing d) →+* universalRing d))))) ↔
      Q (algebraMap R (Carrier (tableOfHom c))) := by
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_universalCarrier c)
  have h2 : P (Spec.map (CommRingCat.ofHom (algebraMap R (Carrier (tableOfHom c))))) ↔
      P (pullback.snd (Spec.map (CommRingCat.ofHom (RingHom.ulift
        (algebraMap (universalRing d) (UniversalFiniteFreeModule d)))))
        (Spec.map (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
          ULift.{u} (universalRing d) →+* universalRing d))))) := by
    rw [← hpb.isoPullback_hom_snd]
    exact MorphismProperty.cancel_left_of_respectsIso P hpb.isoPullback.hom _
  exact h2.symm.trans HasRingHomProperty.Spec_iff

/-- The `Spec` of a composite `φ ∘ c` (precomposed with the lift equivalence) is the composite of
the `Spec`s. -/
private theorem specMap_comp_ulift {S : Type u} [CommRing S]
    (c : universalRing d →+* R) (φ : R →+* S) :
    Spec.map (CommRingCat.ofHom ((φ.comp c).comp
      (ULift.ringEquiv.toRingHom : ULift.{u} (universalRing d) →+* universalRing d))) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (c.comp
        (ULift.ringEquiv.toRingHom : ULift.{u} (universalRing d) →+* universalRing d))) := by
  rw [← Spec.map_comp]
  rfl

/-- A morphism to `X_d` factors through an open subscheme exactly when its image lies there. -/
private theorem factorsThrough_iff_range {T : Scheme.{u}} (U : (scheme.{u} d).Opens)
    (f : T ⟶ scheme.{u} d) :
    (∃ ĝ : T ⟶ U.toScheme, ĝ ≫ U.ι = f) ↔ ∀ t : T, f t ∈ (U : Set (scheme.{u} d)) := by
  constructor
  · rintro ⟨ĝ, rfl⟩ t
    rw [Scheme.Hom.comp_apply]
    exact (ĝ t).2
  · intro h
    have hr : Set.range f ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      exact h t
    exact ⟨IsOpenImmersion.lift U.ι f hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- **Bridge, syntomic case** (Tag 0FL0 on rings). The algebra `B_c` of the table of a ring map
`c : A_d → R` is syntomic over `R` exactly when the morphism `Spec(R) → X_d` defined by `c` maps
every point into `U_d`. -/
theorem syntomic_tableOfHom_iff (c : universalRing d →+* R) :
    Algebra.Syntomic R (Carrier (tableOfHom c)) ↔
      ∀ t : Spec (.of R), Spec.map (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
        ULift.{u} (universalRing d) →+* universalRing d))) t ∈
          (universalSyntomicOpen.{u} d : Set (scheme.{u} d)) := by
  rw [← factorsThrough_iff_range (T := Spec (.of R)), factorsThrough_universalSyntomicOpen_iff,
    universalFamily_pullback_snd_iff (P := @Syntomic), RingHom.syntomic_iff, toAlgebra_algebraMap]

/-- **Bridge, étale case** (Tag 0FL2 on rings). The algebra `B_c` of the table of a ring map
`c : A_d → R` is étale over `R` exactly when every point of `Spec(R)` maps into the étale locus
`U'_d`. -/
theorem etale_tableOfHom_iff (c : universalRing d →+* R) :
    Algebra.Etale R (Carrier (tableOfHom c)) ↔
      ∀ t : Spec (.of R), Spec.map (CommRingCat.ofHom (c.comp (ULift.ringEquiv.toRingHom :
        ULift.{u} (universalRing d) →+* universalRing d))) t ∈
          (universalEtaleOpen.{u} d : Set (scheme.{u} d)) := by
  rw [← factorsThrough_iff_range (T := Spec (.of R)), factorsThrough_universalEtaleOpen_iff,
    universalFamily_pullback_snd_iff (P := @Etale), RingHom.etale_algebraMap]

end Bridge

section Discriminant

variable (d) in
/-- **The universal discriminant**: the discriminant over `A_d` of the distinguished basis of the
universal finite free algebra of rank `d`. -/
def universalDiscr : universalRing d :=
  Algebra.discr (universalRing d) (Carrier.basis (tableOfHom (RingHom.id (universalRing d))))

/-- The basis of the universal carrier `B_d` given by its coordinates. -/
private def universalCarrierBasis :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    Module.Basis (Fin d) (universalRing d) (UniversalFiniteFreeModule d) :=
  letI := (universalAlgebraStructure d).ring
  letI := (universalAlgebraStructure d).algebra
  Module.Basis.ofEquivFun (universalCarrierLinearEquiv d)

/-- The coordinate basis of `B_d` is the family of distinguished basis vectors. -/
private theorem universalCarrierBasis_apply (i : Fin d) :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    universalCarrierBasis i = universalBasisVector d i := by
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  refine universalCarrier_ext fun j => ?_
  simp [universalCarrierBasis, Module.Basis.coe_ofEquivFun, universalCarrierLinearEquiv,
    universalBasisVector, Pi.single_apply, eq_comm]

/-- The discriminant of the universal carrier `B_d`, and its image under a ring map. -/
private theorem discr_tableOfHom_aux {R : Type*} [CommRing R] (c : universalRing d →+* R) :
    letI := (universalAlgebraStructure d).ring
    letI := (universalAlgebraStructure d).algebra
    Algebra.discr R (Carrier.basis (tableOfHom c)) =
      c (Algebra.discr (universalRing d) (universalCarrierBasis (d := d))) := by
  classical
  let := (universalAlgebraStructure d).ring
  let := (universalAlgebraStructure d).algebra
  refine discr_map_of_basis c (universalCarrierClassify d (universalAlgebraStructure d)
    (tableOfHom c)) (fun r => ?_) universalCarrierBasis (Carrier.basis (tableOfHom c))
    (fun i => ?_)
  · rw [universalCarrierClassify_algebraMap, classify_tableOfHom]
  · rw [universalCarrierBasis_apply, universalCarrierClassify_basisVector, Carrier.basis_apply]

/-- **The discriminant of the base change of the universal family.** For a ring map
`c : A_d → R`, the discriminant of the distinguished basis of `B_c` is the image under `c` of the
universal discriminant. -/
theorem discr_tableOfHom {R : Type*} [CommRing R] (c : universalRing d →+* R) :
    Algebra.discr R (Carrier.basis (tableOfHom c)) = c (universalDiscr d) := by
  rw [discr_tableOfHom_aux, universalDiscr, discr_tableOfHom_aux]
  rfl

/-- Tables of ring maps are compatible with extension of scalars. -/
theorem map_tableOfHom {R S : Type*} [CommRing R] [CommRing S] (c : universalRing d →+* R)
    (φ : R →+* S) : FiniteFreeAlgebra.map φ (tableOfHom c) = tableOfHom (φ.comp c) :=
  ext_coeff fun _ _ _ => rfl

/-- **Over a field, an étale finite free algebra has nonzero discriminant**: its trace form is
nondegenerate. -/
@[sga "1 I 4.10" "over a field"]
theorem discr_ne_zero_of_etale {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K B) [Algebra.Etale K B] :
    Algebra.discr K b ≠ 0 := by
  have : FiniteDimensional K B := Module.Finite.of_basis b
  have h := (Stacks.Discriminant.finiteDimensional_etale_iff_traceForm_nondegenerate K B).mp
    inferInstance
  rwa [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b, ← Algebra.traceMatrix_of_basis,
    ← Algebra.discr_def] at h

end Discriminant

section Algebra

/-- **A reduced ring in which `D(a)` is dense**: `a` is a nonzerodivisor. If `a x = 0`, every
prime avoiding `x` would meet `D(a)` in a prime containing neither `a` nor `x`. -/
theorem mem_nonZeroDivisors_of_dense_basicOpen {A : Type*} [CommRing A] [IsReduced A] {a : A}
    (h : Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))) : a ∈ A⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine IsReduced.eq_zero x ((nilpotent_iff_mem_prime).mpr fun J hJ => ?_)
  by_contra hxJ
  obtain ⟨q, hqx, hqa⟩ := h.inter_open_nonempty (PrimeSpectrum.basicOpen x)
    (PrimeSpectrum.basicOpen x).isOpen ⟨⟨J, hJ⟩, hxJ⟩
  have hmem : x * a ∈ q.asIdeal := hx ▸ q.asIdeal.zero_mem
  exact (q.isPrime.mem_or_mem hmem).elim hqx hqa

end Algebra

section Good

variable (d) in
/-- **Syntomic-good elements.** An element `g` of the universal ring `A_d` is *syntomic-good* if
the principal open `D(g)` of `X_d = Spec(A_d)` lies in the open subscheme `U_d` over which the
universal finite free family is syntomic (Tag 0FL0). (The universal ring is lifted to the
universe `u` of the final rings, as it is to form `X_d`.) -/
def IsSyntomicGood (g : universalRing d) : Prop :=
  ∀ x : PrimeSpectrum (ULift.{u} (universalRing d)),
    x ∈ (PrimeSpectrum.basicOpen (ULift.up g) : Set (PrimeSpectrum (ULift.{u} (universalRing d)))) →
      (x : scheme.{u} d) ∈ (universalSyntomicOpen.{u} d : Set (scheme.{u} d))

variable (g : universalRing d)

/-- **The coordinate ring `N_g = A_d[1/g]` of `D(g)`**, in the universe `u`.

It is a type synonym for the localization, carrying only the commutative ring structure, the
algebra structure over the (lifted) universal ring and the localization property: in particular
its only `ℤ`-algebra structure is the canonical one `Ring.toIntAlgebra`, which is the one generic
statements about `Ω[A⁄ℤ]` see. (The `ℤ`-algebra structure inherited from `Localization` is not
definitionally the canonical one.) -/
def universalChartBase : Type u := Localization.Away (ULift.up.{u} g)

/-- The ring structure of `N_g`. -/
instance : CommRing (universalChartBase.{u} g) :=
  inferInstanceAs (CommRing (Localization.Away (ULift.up.{u} g)))

/-- `N_g` is an algebra over the (lifted) universal ring. -/
instance : Algebra (ULift.{u} (universalRing d)) (universalChartBase.{u} g) :=
  inferInstanceAs (Algebra _ (Localization.Away (ULift.up.{u} g)))

/-- `N_g` is the localization of the universal ring away from `g`. -/
instance : IsLocalization.Away (ULift.up.{u} g) (universalChartBase.{u} g) :=
  inferInstanceAs (IsLocalization.Away _ (Localization.Away (ULift.up.{u} g)))

/-- The map `A_d → N_g`. -/
def universalChartBaseClassify : universalRing d →+* universalChartBase.{u} g :=
  (algebraMap (ULift.{u} (universalRing d)) (universalChartBase.{u} g)).comp
      ULift.ringEquiv.symm.toRingHom

/-- The open immersion `D(g) = Spec(N_g) → X_d`, written through the classifying map. -/
private theorem specMap_chartBaseClassify :
    Spec.map (CommRingCat.ofHom ((universalChartBaseClassify.{u} g).comp (ULift.ringEquiv.toRingHom
        :
      ULift.{u} (universalRing d) →+* universalRing d))) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} (universalRing d)) (universalChartBase.{u}
          g))) :=
  rfl

/-- **Good elements, on rings.** `g` is syntomic-good exactly when the base change of the
universal family to `N_g = A_d[1/g]` is syntomic. -/
theorem isSyntomicGood_iff :
    IsSyntomicGood.{u} d g ↔
      Algebra.Syntomic (universalChartBase.{u} g) (Carrier (tableOfHom
          (universalChartBaseClassify.{u} g))) := by
  rw [syntomic_tableOfHom_iff, specMap_chartBaseClassify]
  have hr := PrimeSpectrum.localization_away_comap_range (universalChartBase.{u} g) (ULift.up.{u} g)
  constructor
  · intro hg t
    apply hg
    rw [← hr]
    exact ⟨t, rfl⟩
  · intro h x hx
    rw [← hr] at hx
    obtain ⟨t, rfl⟩ := hx
    exact h t

/-- For a good element, `D(g) = Spec(N_g) → X_d` factors through `U_d` by an open immersion. -/
private theorem exists_isOpenImmersion_universalChartBase_lift (hg : IsSyntomicGood.{u} d g) :
    ∃ ĝ : Spec (.of (universalChartBase.{u} g)) ⟶ (universalSyntomicOpen.{u} d).toScheme,
      IsOpenImmersion ĝ ∧ ĝ ≫ (universalSyntomicOpen.{u} d).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} (universalRing d))
            (universalChartBase.{u} g))) := by
  have h := (syntomic_tableOfHom_iff (universalChartBaseClassify.{u} g)).mp ((isSyntomicGood_iff
      g).mp hg)
  rw [specMap_chartBaseClassify] at h
  obtain ⟨ĝ, hĝ⟩ := (factorsThrough_iff_range _ _).mpr h
  have : IsOpenImmersion (ĝ ≫ (universalSyntomicOpen.{u} d).ι) := by
    rw [hĝ]
    exact IsOpenImmersion.of_isLocalization (ULift.up.{u} g)
  exact ⟨ĝ, IsOpenImmersion.of_comp ĝ (universalSyntomicOpen.{u} d).ι, hĝ⟩

/-- For a good element, `D(g) = Spec(N_g) → X_d` factors through `U_d`. -/
theorem exists_universalChartBase_lift (hg : IsSyntomicGood.{u} d g) :
    ∃ ĝ : Spec (.of (universalChartBase.{u} g)) ⟶ (universalSyntomicOpen.{u} d).toScheme,
      ĝ ≫ (universalSyntomicOpen.{u} d).ι =
        Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} (universalRing d))
            (universalChartBase.{u} g))) :=
  let ⟨ĝ, _, hĝ⟩ := exists_isOpenImmersion_universalChartBase_lift g hg
  ⟨ĝ, hĝ⟩

/-- **`N_g` is smooth over `ℤ`** for a good element `g` (Tag 0FL1): `Spec(N_g)` is an open
subscheme of `U_d`, which is smooth over `Spec(ℤ)`. -/
theorem smooth_universalChartBase (hg : IsSyntomicGood.{u} d g) :
    Algebra.Smooth ℤ (universalChartBase.{u} g) := by
  obtain ⟨ĝ, _, hĝ⟩ := exists_isOpenImmersion_universalChartBase_lift g hg
  have hS : Smooth (ĝ ≫ specULiftZIsTerminal.from (universalSyntomicOpen.{u} d).toScheme) :=
    inferInstance
  let ι0 : ULift.{u} ℤ →+* ℤ := ULift.ringEquiv.toRingHom
  rw [show ĝ ≫ specULiftZIsTerminal.from (universalSyntomicOpen.{u} d).toScheme =
      Spec.map (CommRingCat.ofHom ((algebraMap ℤ (universalChartBase.{u} g)).comp ι0)) from
    specULiftZIsTerminal.hom_ext _ _] at hS
  have h1 : ((algebraMap ℤ (universalChartBase.{u} g)).comp ι0).Smooth :=
      HasRingHomProperty.Spec_iff.mp hS
  have h2 : (algebraMap ℤ (universalChartBase.{u} g)).Smooth := by
    rw [show algebraMap ℤ (universalChartBase.{u} g) =
      ((algebraMap ℤ (universalChartBase.{u} g)).comp ι0).comp
        (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).toRingHom from RingHom.ext_int _ _]
    exact (RingHom.Smooth.of_bijective
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u} ℤ).bijective).comp h1
  exact RingHom.smooth_algebraMap.mp h2

/-- **`N_g` is reduced** for a good element `g`, being smooth over `ℤ`. -/
theorem isReduced_universalChartBase (hg : IsSyntomicGood.{u} d g) :
    IsReduced (universalChartBase.{u} g) := by
  have := smooth_universalChartBase g hg
  exact Algebra.isReduced_of_smooth ℤ (universalChartBase.{u} g)

/-- **`N_g` is Noetherian**, being of finite type over `ℤ`. -/
theorem isNoetherianRing_universalChartBase (hg : IsSyntomicGood.{u} d g) :
    IsNoetherianRing (universalChartBase.{u} g) := by
  have := smooth_universalChartBase g hg
  exact Algebra.FiniteType.isNoetherianRing ℤ (universalChartBase.{u} g)

/-- **The étale locus is dense in `Spec(N_g)` and the discriminant is invertible on it**, so the
principal open of the discriminant is dense in `Spec(N_g)` (Tag 0FL2). -/
theorem dense_basicOpen_discr_universalChartBase (hg : IsSyntomicGood.{u} d g) :
    Dense (PrimeSpectrum.basicOpen (universalChartBaseClassify.{u} g (universalDiscr d)) :
      Set (PrimeSpectrum (universalChartBase.{u} g))) := by
  classical
  obtain ⟨ĝ, _, hĝ⟩ := exists_isOpenImmersion_universalChartBase_lift g hg
  have hdense : Dense (ĝ ⁻¹' ((universalSyntomicOpen.{u} d).ι ⁻¹'
      (universalEtaleOpen.{u} d : Set (scheme.{u} d)))) :=
    (dense_universalEtaleOpen_in_universalSyntomicOpen.{u} d).preimage
      ĝ.isOpenEmbedding.isOpenMap
  refine hdense.mono fun q hq => ?_
  let q0 : Spec (.of (universalChartBase.{u} g)) := q
  let p : PrimeSpectrum (universalChartBase.{u} g) := q
  have hjq : Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} (universalRing d))
      (universalChartBase.{u} g))) q0 ∈ (universalEtaleOpen.{u} d : Set (scheme.{u} d)) := by
    rw [← hĝ, Scheme.Hom.comp_apply]
    exact hq
  let K := p.asIdeal.ResidueField
  let ψ : universalChartBase.{u} g →+* K := algebraMap _ K
  have : Algebra.Etale K (Carrier (tableOfHom (ψ.comp (universalChartBaseClassify.{u} g)))) := by
    rw [etale_tableOfHom_iff]
    intro t
    let t' : PrimeSpectrum K := t
    have : t'.asIdeal.IsPrime := t'.isPrime
    have ht : Spec.map (CommRingCat.ofHom ψ) t = q0 := by
      apply PrimeSpectrum.ext
      change Ideal.comap ψ t'.asIdeal = p.asIdeal
      rw [Ideal.eq_bot_of_prime t'.asIdeal, ← RingHom.ker_eq_comap_bot]
      exact Ideal.ker_algebraMap_residueField _
    rw [specMap_comp_ulift, Scheme.Hom.comp_apply, ht]
    exact hjq
  have hne := discr_ne_zero_of_etale (Carrier.basis (tableOfHom (ψ.comp
      (universalChartBaseClassify.{u} g))))
  rw [discr_tableOfHom, RingHom.comp_apply] at hne
  change universalChartBaseClassify.{u} g (universalDiscr d) ∉ p.asIdeal
  exact fun hmem => hne (Ideal.algebraMap_residueField_eq_zero.mpr hmem)

/-- **The discriminant over `N_g` is a nonzerodivisor** for a good element `g`: `N_g` is reduced
and the principal open of the discriminant is dense. -/
theorem discr_universalChartBase_mem_nonZeroDivisors (hg : IsSyntomicGood.{u} d g) :
    Algebra.discr (universalChartBase.{u} g) (Carrier.basis (tableOfHom
        (universalChartBaseClassify.{u} g))) ∈
      (universalChartBase.{u} g)⁰ := by
  have := isReduced_universalChartBase g hg
  rw [discr_tableOfHom]
  exact mem_nonZeroDivisors_of_dense_basicOpen (dense_basicOpen_discr_universalChartBase g hg)

end Good

section Charts

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Syntomicity of `B_c` ascends along any ring map.** -/
theorem syntomic_tableOfHom_comp (c : universalRing d →+* R) (φ : R →+* S)
    [Algebra.Syntomic R (Carrier (tableOfHom c))] :
    Algebra.Syntomic S (Carrier (tableOfHom (φ.comp c))) := by
  have h := (syntomic_tableOfHom_iff c).mp inferInstance
  rw [syntomic_tableOfHom_iff]
  intro t
  rw [specMap_comp_ulift, Scheme.Hom.comp_apply]
  exact h _

/-- **If `g` is good and `c g` is a unit, `B_c` is syntomic**: `c` factors through `N_g`. -/
theorem syntomic_tableOfHom_of_isUnit {g : universalRing d} (hg : IsSyntomicGood.{u} d g)
    (c : universalRing d →+* R) (hc : IsUnit (c g)) :
    Algebra.Syntomic R (Carrier (tableOfHom c)) := by
  have := (isSyntomicGood_iff g).mp hg
  let c' : ULift.{u} (universalRing d) →+* R :=
    c.comp (ULift.ringEquiv.toRingHom : ULift.{u} (universalRing d) →+* universalRing d)
  let φ : universalChartBase.{u} g →+* R := IsLocalization.Away.lift (ULift.up g) (g := c') hc
  have hφ : φ.comp (universalChartBaseClassify.{u} g) = c :=
    RingHom.ext fun a => IsLocalization.Away.lift_eq (ULift.up g) hc (ULift.up a)
  rw [← hφ]
  exact syntomic_tableOfHom_comp _ _

end Charts

section PolynomialChart

variable (σ : Type u) (R : Type u) [CommRing R]

/-- **A polynomial chart** `R[x_σ]`, the polynomial ring over `R` in the variables `σ` (any type).

It is a type synonym for `MvPolynomial σ R` carrying only its commutative ring and `R`-algebra
structures, so that its only `ℤ`-algebra structure is the canonical one `Ring.toIntAlgebra`, which
is the one generic statements about `Ω[A⁄ℤ]` see. -/
def polynomialChart : Type u := MvPolynomial σ R

/-- The ring structure of a polynomial chart. -/
instance : CommRing (polynomialChart σ R) := inferInstanceAs (CommRing (MvPolynomial σ R))

/-- A polynomial chart is an algebra over its base. -/
instance : Algebra R (polynomialChart σ R) := inferInstanceAs (Algebra R (MvPolynomial σ R))

/-- A polynomial chart is flat over its base. -/
instance : Module.Flat R (polynomialChart σ R) := inferInstanceAs (Module.Flat R (MvPolynomial σ R))

/-- A polynomial chart is formally smooth over its base. -/
instance : Algebra.FormallySmooth R (polynomialChart σ R) :=
  inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial σ R))

variable {σ R}

/-- **A polynomial chart over a formally smooth ring is formally smooth over `ℤ`**, so its module
of differentials is projective. -/
theorem polynomialChart_formallySmooth [Algebra.FormallySmooth ℤ R] :
    Algebra.FormallySmooth ℤ (polynomialChart σ R) :=
  Algebra.FormallySmooth.comp ℤ R (polynomialChart σ R)

/-- **A polynomial chart over a smooth ring, in finitely many variables, is smooth over `ℤ`.** -/
theorem polynomialChart_smooth [Finite σ] [Algebra.Smooth ℤ R] :
    Algebra.Smooth ℤ (polynomialChart σ R) := by
  have : Algebra.Smooth R (polynomialChart σ R) :=
    { formallySmooth := inferInstance
      finitePresentation := inferInstanceAs (Algebra.FinitePresentation R (MvPolynomial σ R)) }
  exact Algebra.Smooth.comp ℤ R (polynomialChart σ R)

/-- **A polynomial chart over a Noetherian ring, in finitely many variables, is Noetherian.** -/
theorem polynomialChart_isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (polynomialChart σ R) :=
  inferInstanceAs (IsNoetherianRing (MvPolynomial σ R))

/-- **The discriminant over a polynomial chart** of the base change of the universal family is
the image of the discriminant over the base. -/
theorem discr_polynomialChart (c : universalRing d →+* R) :
    Algebra.discr (polynomialChart σ R)
        (Carrier.basis (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c))) =
      algebraMap R (polynomialChart σ R) (Algebra.discr R (Carrier.basis (tableOfHom c))) := by
  rw [discr_tableOfHom, discr_tableOfHom]
  rfl

/-- **Nice elements on polynomial charts** (Stacks 0FLB, 0FLC). If `R` is formally smooth over
`ℤ` and the discriminant `Δ` of the base change `B_c` of the universal family along
`c : A_d → R` is a nonzerodivisor, then over every polynomial chart `R[x_σ]` the discriminant of
the base change of the universal family, which is the image of `Δ`, is a nice element. -/
theorem discr_polynomialChart_nice [Algebra.FormallySmooth ℤ R] (c : universalRing d →+* R)
    (hc : Algebra.discr R (Carrier.basis (tableOfHom c)) ∈ R⁰) :
    IsNiceElement (polynomialChart σ R)
      (Carrier (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c)))
      (Algebra.discr (polynomialChart σ R)
        (Carrier.basis (tableOfHom ((algebraMap R (polynomialChart σ R)).comp c)))) := by
  have := polynomialChart_formallySmooth (σ := σ) (R := R)
  refine discr_nice _ ?_
  rw [discr_polynomialChart]
  exact algebraMap_mem_nonZeroDivisors_of_flat hc

end PolynomialChart

section UniversalCharts

variable (σ : Type u) (g : universalRing d)

/-- **The universal chart ring** `R = N_g[x_σ]`, for any type of variables `σ`. -/
abbrev universalChartRing : Type u := polynomialChart σ (universalChartBase.{u} g)

/-- The classifying map `A_d → R = N_g[x_σ]` of the base change of the universal family. -/
def universalChartClassify : universalRing d →+* universalChartRing σ g :=
  (algebraMap (universalChartBase.{u} g) (universalChartRing σ g)).comp
    (universalChartBaseClassify.{u} g)

variable {g}

/-- **The universal chart ring is formally smooth over `ℤ`**, for any set of variables. -/
theorem universalChartRing_formallySmooth (hg : IsSyntomicGood.{u} d g) :
    Algebra.FormallySmooth ℤ (universalChartRing σ g) := by
  have := smooth_universalChartBase g hg
  exact polynomialChart_formallySmooth

/-- **The universal chart ring has projective differentials over `ℤ`.** -/
theorem universalChartRing_projective_kaehler (hg : IsSyntomicGood.{u} d g) :
    Module.Projective (universalChartRing σ g) Ω[universalChartRing σ g⁄ℤ] := by
  have := universalChartRing_formallySmooth σ hg
  infer_instance

/-- **The universal chart ring in finitely many variables is smooth over `ℤ`.** -/
theorem universalChartRing_smooth [Finite σ] (hg : IsSyntomicGood.{u} d g) :
    Algebra.Smooth ℤ (universalChartRing σ g) := by
  have := smooth_universalChartBase g hg
  exact polynomialChart_smooth

/-- **The universal chart ring in finitely many variables is Noetherian.** -/
theorem universalChartRing_isNoetherianRing [Finite σ] (hg : IsSyntomicGood.{u} d g) :
    IsNoetherianRing (universalChartRing σ g) := by
  have := isNoetherianRing_universalChartBase g hg
  exact polynomialChart_isNoetherianRing

/-- **The universal algebra over the universal chart ring is syntomic.** -/
theorem universalChartRing_syntomic (hg : IsSyntomicGood.{u} d g) :
    Algebra.Syntomic (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
        := by
  have := (isSyntomicGood_iff g).mp hg
  exact syntomic_tableOfHom_comp _ _

/-- **The discriminant over the universal chart ring is a nonzerodivisor**: it is the image of
the discriminant over `N_g`, a nonzerodivisor, under the flat map `N_g → N_g[x_σ]`. -/
theorem discr_universalChartRing_mem_nonZeroDivisors (hg : IsSyntomicGood.{u} d g) :
    Algebra.discr (universalChartRing σ g)
        (Carrier.basis (tableOfHom (universalChartClassify σ g))) ∈ (universalChartRing σ g)⁰ := by
  rw [universalChartClassify, discr_polynomialChart]
  exact algebraMap_mem_nonZeroDivisors_of_flat (discr_universalChartBase_mem_nonZeroDivisors g hg)

/-- **Universal nice charts** (Stacks 0FLB, 0FLC). For a syntomic-good `g` and any set of
variables `σ`, over `R = N_g[x_σ]` the discriminant `Δ` of the distinguished basis of the base
change `B_R` of the universal family is a nice element: a nonzerodivisor on every `Ω^p_R`, a power
of it kills `Ω_{B_R/R}`, and the kernel of `B_R ⊗_R Ω_{R/ℤ} → Ω_{B_R/ℤ}` is `Δ`-power torsion. -/
theorem discr_universalChartRing_nice (hg : IsSyntomicGood.{u} d g) :
    IsNiceElement (universalChartRing σ g) (Carrier (tableOfHom (universalChartClassify σ g)))
      (Algebra.discr (universalChartRing σ g)
        (Carrier.basis (tableOfHom (universalChartClassify σ g)))) := by
  have := smooth_universalChartBase g hg
  exact discr_polynomialChart_nice _ (discr_universalChartBase_mem_nonZeroDivisors g hg)

end UniversalCharts


end Stacks.FormsTrace

end
