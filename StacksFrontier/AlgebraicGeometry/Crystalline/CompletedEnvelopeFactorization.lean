module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.CompletedSetIndexedUniversalProperty

/-!
# The factorization `ρ = τ ∘ σ` through the completed divided power polynomial algebra

Let `(A, I, γ)` be a divided power ring, let `P = A[x_i : i ∈ ι]` be a polynomial algebra over
it, let `J ⊆ P` be an ideal containing `I P`, let `E = D_{P,γ}(J)` be the divided power envelope
of [Stacks, Tag 07H8] and let `D` be the `p`-adic completion of `E`, a divided power ring by
[Stacks, Tag 07KD].  This is the ring `D` of [Stacks, Proposition 60.21.3, Tag 07LG] and of
[Stacks, Lemma 60.21.4, Tag 07LH].

A divided power `A`-algebra endomorphism `ρ` of `D` compatible with the augmentation, writing
`ρ(x_i) = x_i + z_i`, factors as `D --σ--> D⟨ξ_i⟩^∧ --τ--> D`, where `D⟨ξ_i⟩^∧` is the `p`-adic
completion of the divided power polynomial algebra over `D`, `σ(x_i) = x_i + ξ_i` and `τ` is the
divided power `D`-algebra map with `τ(ξ_i) = z_i`; and `D⟨ξ_i⟩^∧` has an automorphism `α` with
`α(x_i) = x_i - ξ_i` and `α(ξ_i) = ξ_i`.

## Main definitions

* `Crystalline.IsAugmentationCompatible` — an endomorphism `ρ` of a divided power ring
  `(R, I, γ)` with `ρ(d) - d ∈ I` for every `d`.
* `Crystalline.envelopeCompletion` — the ring `D`.
* `Crystalline.envelopeCompletionVariableRing` — the ring `D⟨ξ_i⟩^∧`.
* `Crystalline.envelopeCompletionNu` — `ν : D → D⟨ξ_i⟩^∧`, the structure map.
* `Crystalline.envelopeCompletionSigma` — `σ : D → D⟨ξ_i⟩^∧`, `x_i ↦ x_i + ξ_i`.
* `Crystalline.envelopeCompletionSigmaNeg` — `σ⁻ : D → D⟨ξ_i⟩^∧`, `x_i ↦ x_i - ξ_i`.
* `Crystalline.envelopeCompletionTau` — `τ : D⟨ξ_i⟩^∧ → D`, the divided power `D`-algebra map
  with `ξ_i ↦ z_i`.
* `Crystalline.envelopeCompletionAlpha` and `Crystalline.envelopeCompletionAlphaInv` — the
  automorphism `α` of `D⟨ξ_i⟩^∧` with `α(x_i) = x_i - ξ_i`, `α(ξ_i) = ξ_i`, and its inverse
  `x_i ↦ x_i + ξ_i`, `ξ_i ↦ ξ_i`.

## Main results

* `Crystalline.existsUnique_dPMorphism_from_envelopeCompletion` — the universal property of `D`.
* `Crystalline.envelopeCompletionTau_comp_sigma` — `τ ∘ σ = ρ`.
* `Crystalline.envelopeCompletionAlpha_comp_sigma` — `α ∘ σ = ν`.
* `Crystalline.envelopeCompletionTau_comp_nu` — `τ ∘ ν = id_D`.
* `Crystalline.envelopeCompletionAlpha_comp_alphaInv` and
  `Crystalline.envelopeCompletionAlphaInv_comp_alpha` — `α` is an automorphism.
* `Crystalline.exists_factorization_of_isAugmentationCompatible` — all of these in one statement.

## References

* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

namespace Crystalline

open DividedPowers

universe u

/-- **Compatibility of an endomorphism of a divided power ring with its augmentation.**  The
augmentation of the divided power ring `(R, I, γ)` is the reduction `R → R ⧸ I`; an endomorphism
is compatible with it exactly when it induces the identity on `R ⧸ I`, that is when it moves
every element by an element of `I`. -/
public def IsAugmentationCompatible {R : Type u} [CommRing R] {I : Ideal R}
    {γ : _root_.DividedPowers I} (ρ : _root_.DividedPowers.DPMorphism γ γ) : Prop :=
  ∀ x : R, ρ x - x ∈ I

/-! ### The completed divided power envelope of a polynomial presentation -/

section EnvelopeCompletion

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **The ring `D`**: the `p`-adic completion of the divided power envelope of a polynomial
presentation, as a divided power ring. -/
public def envelopeCompletion : DividedPowerRing.{u} :=
  .of (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) (E.object : Type u))
    (completionIdeal E.object.ideal p hp)
    (completedDividedPowers E.object.ideal E.object.dividedPowers p hp).1

/-- `D` is `p`-adically complete, being a `p`-adic completion. -/
public theorem isAdicCompleteEnvelopeCompletion :
    IsAdicComplete (pAdicIdeal (A := (envelopeCompletion E p hp : Type u)) p)
      (envelopeCompletion E p hp : Type u) :=
  isAdicComplete_pAdicIdeal_adicCompletion (R := (E.object : Type u)) p

attribute [instance] isAdicCompleteEnvelopeCompletion

/-- `D` is an algebra over the envelope, being its `p`-adic completion. -/
@[instance_reducible]
public def algebraEnvelopeCompletion :
    Algebra (E.object : Type u) (envelopeCompletion E p hp : Type u) :=
  inferInstanceAs (Algebra (E.object : Type u)
    (AdicCompletion (pAdicIdeal (A := (E.object : Type u)) p) (E.object : Type u)))

attribute [instance] algebraEnvelopeCompletion

/-- The structure map `E → D` of the `p`-adic completion, as a divided power morphism. -/
public abbrev envelopeCompletionInclusion :
    DPMorphism E.object.dividedPowers (envelopeCompletion E p hp).dividedPowers :=
  completionDPMorphism E.object.ideal E.object.dividedPowers p hp

/-- The structure map `A → D`, the envelope's structure map followed by the completion. -/
public abbrev envelopeCompletionStructureMap :
    DPMorphism A.dividedPowers (envelopeCompletion E p hp).dividedPowers :=
  (envelopeCompletionInclusion E p hp).comp E.structureMap

/-- **The coordinate `x_i` in `D`**: the image of the polynomial variable `X i` under
`P → E → D`. -/
public def envelopeCompletionCoord (i : ι) : envelopeCompletion E p hp :=
  envelopeCompletionInclusion E p hp (E.algebraMap.toRingHom (MvPolynomial.X i))

/-- `p` is nilpotent modulo the divided power ideal of `D`. -/
public theorem isNilpotent_mk_envelopeCompletion :
    IsNilpotent (Ideal.Quotient.mk (envelopeCompletion E p hp).ideal
      (p : envelopeCompletion E p hp)) :=
  isNilpotent_mk_completionIdeal E.object.ideal p hp

/-- **The universal property of `D`.**

A divided power morphism out of the `p`-adic completion `D` of the divided power envelope of a
polynomial presentation `A[x_i] ⊇ J`, into a `p`-adically complete divided power ring `T`, is
determined by its restriction `A → T` and by the images of the coordinates `x_i`; and it exists
for every such datum whose induced ring map `A[x_i] → T` carries `J` into the divided power
ideal of `T`. -/
public theorem existsUnique_dPMorphism_from_envelopeCompletion [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (E.object : Type u)]
    (T : DividedPowerRing.{u}) [Algebra (IntegersAtPrime p) (T : Type u)]
    (hpT : IsNilpotent (Ideal.Quotient.mk T.ideal (p : T)))
    [IsAdicComplete (pAdicIdeal (A := (T : Type u)) p) (T : Type u)]
    (a : DPMorphism A.dividedPowers T.dividedPowers) (v : ι → T)
    (hv : J.map (MvPolynomial.eval₂Hom a.toRingHom v) ≤ T.ideal) :
    ∃! g : DPMorphism (envelopeCompletion E p hp).dividedPowers T.dividedPowers,
      g.comp (envelopeCompletionStructureMap E p hp) = a ∧
        ∀ i : ι, g (envelopeCompletionCoord E p hp i) = v i := by
  classical
  have hcomp : (MvPolynomial.eval₂Hom a.toRingHom v).comp
      (algebraMap A (MvPolynomial ι A)) = a.toRingHom := by
    ext x
    simp
  set t : IdealPair.HomOver (IdealPair.Hom.ofRingHom (algebraMap A (MvPolynomial ι A)) hJ)
      (IdealPair.Hom.ofDPMorphism a) :=
    ⟨IdealPair.Hom.ofRingHom (MvPolynomial.eval₂Hom a.toRingHom v) hv,
      IdealPair.Hom.ext_toRingHom _ _ hcomp⟩
  set q := (E.homEquiv T a).symm t
  have hqalg : q.1.toRingHom.comp E.algebraMap.toRingHom =
      MvPolynomial.eval₂Hom a.toRingHom v := by
    have hval := E.homEquiv_apply T a q
    rw [(E.homEquiv T a).apply_symm_apply t] at hval
    exact (congrArg IdealPair.Hom.toRingHom hval).symm
  obtain ⟨g, hg, hguniq⟩ := existsUnique_dPMorphism_comp_completionDPMorphism
    E.object.ideal E.object.dividedPowers T.ideal T.dividedPowers p hp hpT q.1
  have hgval (x : E.object) : g (envelopeCompletionInclusion E p hp x) = q.1 x :=
    DFunLike.congr_fun hg x
  refine ⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · apply DPMorphism.ext
    funext x
    exact (hgval (E.structureMap x)).trans (DFunLike.congr_fun q.2 x)
  · refine (hgval (E.algebraMap.toRingHom (MvPolynomial.X i))).trans ?_
    simpa using congrArg (fun r : MvPolynomial ι A →+* T ↦ r (MvPolynomial.X i)) hqalg
  · rintro g' ⟨hgstr, hgcoord⟩
    refine hguniq g' ?_
    have hq'str : (g'.comp (envelopeCompletionInclusion E p hp)).comp
        E.structureMap = a := by
      apply DPMorphism.ext
      funext x
      exact DFunLike.congr_fun hgstr x
    have hq'alg : (g'.comp (envelopeCompletionInclusion E p hp)).toRingHom.comp
        E.algebraMap.toRingHom = MvPolynomial.eval₂Hom a.toRingHom v := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change g' (envelopeCompletionInclusion E p hp
          (E.algebraMap.toRingHom (MvPolynomial.C r))) = _
        rw [show E.algebraMap.toRingHom (MvPolynomial.C r) = E.structureMap.toRingHom r from
          RingHom.congr_fun E.algebraMap_comp r]
        exact (DFunLike.congr_fun hgstr r).trans (RingHom.congr_fun hcomp r).symm
      · intro i
        change g' (envelopeCompletionInclusion E p hp
          (E.algebraMap.toRingHom (MvPolynomial.X i))) = _
        rw [show MvPolynomial.eval₂Hom a.toRingHom v (MvPolynomial.X i) = v i by simp]
        exact hgcoord i
    have himg : E.homEquiv T a ⟨g'.comp (envelopeCompletionInclusion E p hp),
        hq'str⟩ = E.homEquiv T a q := by
      apply Subtype.ext
      apply IdealPair.Hom.ext_toRingHom
      rw [E.homEquiv_apply T a ⟨_, hq'str⟩, E.homEquiv_apply T a q]
      change (g'.comp (envelopeCompletionInclusion E p hp)).toRingHom.comp
          E.algebraMap.toRingHom = q.1.toRingHom.comp E.algebraMap.toRingHom
      rw [hq'alg, hqalg]
    exact congrArg Subtype.val ((E.homEquiv T a).injective himg)

/-! ### The universal property of `D` as a construction -/

section Lift

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]
  (T : DividedPowerRing.{u}) [Algebra (IntegersAtPrime p) (T : Type u)]
  (hpT : IsNilpotent (Ideal.Quotient.mk T.ideal (p : T)))
  [IsAdicComplete (pAdicIdeal (A := (T : Type u)) p) (T : Type u)]
  (a : DPMorphism A.dividedPowers T.dividedPowers) (v : ι → T)
  (hv : J.map (MvPolynomial.eval₂Hom a.toRingHom v) ≤ T.ideal)

/-- **The divided power morphism `D → T` over `A` with prescribed values on the coordinates**,
supplied by `Crystalline.existsUnique_dPMorphism_from_envelopeCompletion`. -/
public def envelopeCompletionLift :
    DPMorphism (envelopeCompletion E p hp).dividedPowers T.dividedPowers :=
  (existsUnique_dPMorphism_from_envelopeCompletion E p hp T hpT a v hv).choose

/-- The lift restricts to `a` on the base. -/
public theorem envelopeCompletionLift_comp_structureMap :
    (envelopeCompletionLift E p hp T hpT a v hv).comp
        (envelopeCompletionStructureMap E p hp) = a :=
  ((existsUnique_dPMorphism_from_envelopeCompletion E p hp T hpT a v hv).choose_spec).1.1

/-- The lift sends the coordinate `x_i` to `v i`. -/
public theorem envelopeCompletionLift_coord (i : ι) :
    envelopeCompletionLift E p hp T hpT a v hv
        (envelopeCompletionCoord E p hp i) = v i :=
  ((existsUnique_dPMorphism_from_envelopeCompletion E p hp T hpT a v
    hv).choose_spec).1.2 i

/-- The lift is the only divided power morphism over `A` with those values on the
coordinates. -/
public theorem eq_envelopeCompletionLift
    (g : DPMorphism (envelopeCompletion E p hp).dividedPowers T.dividedPowers)
    (hga : g.comp (envelopeCompletionStructureMap E p hp) = a)
    (hgv : ∀ i : ι, g (envelopeCompletionCoord E p hp i) = v i) :
    g = envelopeCompletionLift E p hp T hpT a v hv :=
  ((existsUnique_dPMorphism_from_envelopeCompletion E p hp T hpT a v
    hv).choose_spec).2 g ⟨hga, hgv⟩

end Lift

/-! ### Shifting the coordinates by elements of the divided power ideal -/

/-- **The compatibility the universal property of `D` asks for is automatic when the prescribed
values differ from the values of an existing morphism by elements of the divided power ideal.**

If `m : D → T` is a divided power morphism over `a : A → T` and `v i - m(x_i)` lies in the
divided power ideal of `T` for every `i`, then the polynomial map `A[x_i] → T` sending `x_i` to
`v i` carries `J` into the divided power ideal of `T`. -/
public theorem eval₂Hom_map_le_of_sub_mem (T : DividedPowerRing.{u})
    (m : DPMorphism (envelopeCompletion E p hp).dividedPowers T.dividedPowers)
    (a : DPMorphism A.dividedPowers T.dividedPowers)
    (ha : m.comp (envelopeCompletionStructureMap E p hp) = a)
    (v : ι → T) (hv : ∀ i : ι, v i - m (envelopeCompletionCoord E p hp i) ∈ T.ideal) :
    J.map (MvPolynomial.eval₂Hom a.toRingHom v) ≤ T.ideal := by
  classical
  set w : MvPolynomial ι A →+* T :=
    m.toRingHom.comp ((envelopeCompletionInclusion E p hp).toRingHom.comp
      E.algebraMap.toRingHom)
  have hwC (r : A) : w (MvPolynomial.C r) = a r := by
    change m ((envelopeCompletionInclusion E p hp)
      (E.algebraMap.toRingHom (MvPolynomial.C r))) = a r
    rw [show E.algebraMap.toRingHom (MvPolynomial.C r) = E.structureMap.toRingHom r from
      RingHom.congr_fun E.algebraMap_comp r]
    exact DFunLike.congr_fun ha r
  have hwJ (x : MvPolynomial ι A) (hx : x ∈ J) : w x ∈ T.ideal :=
    m.ideal_comp (Ideal.mem_map_of_mem _
      ((envelopeCompletionInclusion E p hp).ideal_comp (Ideal.mem_map_of_mem _
        (E.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hx)))))
  have hmod : (Ideal.Quotient.mk T.ideal).comp (MvPolynomial.eval₂Hom a.toRingHom v) =
      (Ideal.Quotient.mk T.ideal).comp w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change Ideal.Quotient.mk T.ideal (MvPolynomial.eval₂Hom a.toRingHom v
        (MvPolynomial.C r)) = Ideal.Quotient.mk T.ideal (w (MvPolynomial.C r))
      rw [hwC r]
      simp
    · intro i
      change Ideal.Quotient.mk T.ideal (MvPolynomial.eval₂Hom a.toRingHom v
        (MvPolynomial.X i)) = Ideal.Quotient.mk T.ideal (w (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X']
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hv i)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hdiff : MvPolynomial.eval₂Hom a.toRingHom v x - w x ∈ T.ideal :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (RingHom.congr_fun hmod x)
  simpa using T.ideal.add_mem hdiff (hwJ x hx)

/-- Two divided power morphisms out of `D` that agree on the base `A` and on the coordinates `x_i`
are equal. -/
private theorem eq_of_apply_structureMap_of_apply_coord [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (E.object : Type u)]
    (T : DividedPowerRing.{u}) [Algebra (IntegersAtPrime p) (T : Type u)]
    (hpT : IsNilpotent (Ideal.Quotient.mk T.ideal (p : T)))
    [IsAdicComplete (pAdicIdeal (A := (T : Type u)) p) (T : Type u)]
    (g m : DPMorphism (envelopeCompletion E p hp).dividedPowers T.dividedPowers)
    (hg : ∀ x, g (envelopeCompletionStructureMap E p hp x) =
      m (envelopeCompletionStructureMap E p hp x))
    (hc : ∀ i, g (envelopeCompletionCoord E p hp i) = m (envelopeCompletionCoord E p hp i)) :
    g = m := by
  have hv := eval₂Hom_map_le_of_sub_mem E p hp T m _ rfl
    (fun i ↦ m (envelopeCompletionCoord E p hp i)) (fun i ↦ by simp)
  refine (eq_envelopeCompletionLift E p hp T hpT _ _ hv g
    (DPMorphism.ext (funext hg)) hc).trans
    (eq_envelopeCompletionLift E p hp T hpT _ _ hv m rfl (fun _ ↦ rfl)).symm

end EnvelopeCompletion

/-! ### Divided power morphisms as additive maps -/

private theorem dPMorphism_map_add {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {K : Ideal S} {γ : _root_.DividedPowers I} {δ : _root_.DividedPowers K}
    (f : _root_.DividedPowers.DPMorphism γ δ) (x y : R) : f (x + y) = f x + f y :=
  f.toRingHom.map_add x y

private theorem dPMorphism_map_sub {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {K : Ideal S} {γ : _root_.DividedPowers I} {δ : _root_.DividedPowers K}
    (f : _root_.DividedPowers.DPMorphism γ δ) (x y : R) : f (x - y) = f x - f y :=
  f.toRingHom.map_sub x y

private theorem dPMorphism_id_comp {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    {K : Ideal S} {γ : _root_.DividedPowers I} {δ : _root_.DividedPowers K}
    (f : _root_.DividedPowers.DPMorphism γ δ) :
    (_root_.DividedPowers.DPMorphism.id δ).comp f = f :=
  rfl

/-! ### The divided power polynomial algebra on the variables `ξ_i` over `D` -/

section Factorization

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))

/-- **The ring `D⟨ξ_i : i ∈ ι⟩^∧`**: the `p`-adic completion of the divided power polynomial
algebra over `D` on one variable `ξ_i` for each coordinate `x_i`.

Its underlying ring is the same as
`Crystalline.DividedPowerPolynomial.completedDividedPowerPolynomialRing D ι p`. -/
public abbrev envelopeCompletionVariableRing : DividedPowerRing.{u} :=
  .of (AdicCompletion (pAdicIdeal
        (A := setIndexedDividedPowerPolynomialAlgebra (envelopeCompletion E p hp) ι) p)
      (setIndexedDividedPowerPolynomialAlgebra (envelopeCompletion E p hp) ι))
    (completionIdeal (dividedPowerPolynomialIdeal (envelopeCompletion E p hp).ideal ι) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal (envelopeCompletion E p hp) ι p
        (isNilpotent_mk_envelopeCompletion E p hp)))
    (completedDividedPowers (dividedPowerPolynomialIdeal (envelopeCompletion E p hp).ideal ι)
      (setIndexedDividedPowerPolynomialDividedPowers (envelopeCompletion E p hp) ι) p
      (isNilpotent_mk_dividedPowerPolynomialIdeal (envelopeCompletion E p hp) ι p
        (isNilpotent_mk_envelopeCompletion E p hp))).1

/-- `p` is nilpotent modulo the divided power ideal of `D⟨ξ_i⟩^∧`. -/
public theorem isNilpotent_mk_envelopeCompletionVariableRing :
    IsNilpotent (Ideal.Quotient.mk (envelopeCompletionVariableRing E p hp).ideal
      (p : envelopeCompletionVariableRing E p hp)) :=
  isNilpotent_mk_completionIdeal (dividedPowerPolynomialIdeal (envelopeCompletion E p hp).ideal ι) p
    (isNilpotent_mk_dividedPowerPolynomialIdeal (envelopeCompletion E p hp) ι p
      (isNilpotent_mk_envelopeCompletion E p hp))

/-- **The structure map `ν : D → D⟨ξ_i⟩^∧`.** -/
public abbrev envelopeCompletionNu :
    DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers :=
  completedSetIndexedDividedPowerPolynomialCoefficientDPMorphism (envelopeCompletion E p hp) ι p
    (isNilpotent_mk_envelopeCompletion E p hp)

/-- **The variable `ξ_i` of `D⟨ξ_i⟩^∧`.** -/
public abbrev envelopeCompletionXi (i : ι) : envelopeCompletionVariableRing E p hp :=
  completedSetIndexedDividedPowerPolynomialVariable (envelopeCompletion E p hp) ι p i

/-- The variables `ξ_i` lie in the divided power ideal of `D⟨ξ_i⟩^∧`. -/
public theorem envelopeCompletionXi_mem (i : ι) :
    envelopeCompletionXi E p hp i ∈ (envelopeCompletionVariableRing E p hp).ideal :=
  completedSetIndexedDividedPowerPolynomialVariable_mem (envelopeCompletion E p hp) ι p
    (isNilpotent_mk_envelopeCompletion E p hp) i

/-! ### The `ℤ_(p)`-algebra structures carried along -/

section Instances

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]

/-- The `ℤ_(p)`-algebra structure on `D`, carried from the envelope. -/
@[instance_reducible]
public def integersAtPrimeAlgebraCompletion :
    Algebra (IntegersAtPrime p) (envelopeCompletion E p hp) :=
  ((algebraMap (E.object : Type u) (envelopeCompletion E p hp)).comp
    (algebraMap (IntegersAtPrime p) (E.object : Type u))).toAlgebra

attribute [instance] integersAtPrimeAlgebraCompletion

/-- The `ℤ_(p)`-algebra structure on `D⟨ξ_i⟩^∧`, carried from `D`. -/
@[instance_reducible]
public def integersAtPrimeAlgebraVariableRing :
    Algebra (IntegersAtPrime p) (envelopeCompletionVariableRing E p hp) :=
  ((algebraMap (setIndexedDividedPowerPolynomialAlgebra (envelopeCompletion E p hp) ι)
        (envelopeCompletionVariableRing E p hp)).comp
    ((algebraMap (envelopeCompletion E p hp) (setIndexedDividedPowerPolynomialAlgebra
        (envelopeCompletion E p hp) ι)).comp
      (algebraMap (IntegersAtPrime p) (envelopeCompletion E p hp)))).toAlgebra

attribute [instance] integersAtPrimeAlgebraVariableRing

/-! ### The maps `σ`, `σ⁻`, `τ`, `α` and `α⁻¹` -/

/-- **`σ : D → D⟨ξ_i⟩^∧`**, the divided power `A`-algebra map with `σ(x_i) = x_i + ξ_i`. -/
public def envelopeCompletionSigma :
    DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers :=
  envelopeCompletionLift E p hp (envelopeCompletionVariableRing E p hp)
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp)
    ((envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp))
    (fun i ↦ envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) +
      envelopeCompletionXi E p hp i)
    (eval₂Hom_map_le_of_sub_mem E p hp (envelopeCompletionVariableRing E p hp)
      (envelopeCompletionNu E p hp) _ rfl _ (fun i ↦ by
        simpa using envelopeCompletionXi_mem E p hp i))

/-- **`σ⁻ : D → D⟨ξ_i⟩^∧`**, the divided power `A`-algebra map with `σ⁻(x_i) = x_i - ξ_i`.  It
is the coefficient restriction of the automorphism `α`. -/
public def envelopeCompletionSigmaNeg :
    DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers :=
  envelopeCompletionLift E p hp (envelopeCompletionVariableRing E p hp)
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp)
    ((envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp))
    (fun i ↦ envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) -
      envelopeCompletionXi E p hp i)
    (eval₂Hom_map_le_of_sub_mem E p hp (envelopeCompletionVariableRing E p hp)
      (envelopeCompletionNu E p hp) _ rfl _ (fun i ↦ by
        simpa using envelopeCompletionXi_mem E p hp i))

/-- `σ` restricts to `ν` on the base `A`. -/
public theorem envelopeCompletionSigma_comp_structureMap :
    (envelopeCompletionSigma E p hp).comp (envelopeCompletionStructureMap E p hp) =
      (envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp) :=
  envelopeCompletionLift_comp_structureMap E p hp _ _ _ _ _

/-- `σ(x_i) = x_i + ξ_i`. -/
public theorem envelopeCompletionSigma_coord (i : ι) :
    envelopeCompletionSigma E p hp (envelopeCompletionCoord E p hp i) =
      envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) +
          envelopeCompletionXi E p hp i :=
  envelopeCompletionLift_coord E p hp _ _ _ _ _ i

/-- `σ⁻` restricts to `ν` on the base `A`. -/
public theorem envelopeCompletionSigmaNeg_comp_structureMap :
    (envelopeCompletionSigmaNeg E p hp).comp (envelopeCompletionStructureMap E p hp) =
      (envelopeCompletionNu E p hp).comp (envelopeCompletionStructureMap E p hp) :=
  envelopeCompletionLift_comp_structureMap E p hp _ _ _ _ _

/-- `σ⁻(x_i) = x_i - ξ_i`. -/
public theorem envelopeCompletionSigmaNeg_coord (i : ι) :
    envelopeCompletionSigmaNeg E p hp (envelopeCompletionCoord E p hp i) =
      envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) -
          envelopeCompletionXi E p hp i :=
  envelopeCompletionLift_coord E p hp _ _ _ _ _ i

/-- **`α : D⟨ξ_i⟩^∧ → D⟨ξ_i⟩^∧`**, the divided power morphism with `α(x_i) = x_i - ξ_i` and
`α(ξ_i) = ξ_i`. -/
public def envelopeCompletionAlpha :
    DPMorphism (envelopeCompletionVariableRing E p hp).dividedPowers
      (envelopeCompletionVariableRing E p hp).dividedPowers :=
  completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
    (envelopeCompletionVariableRing E p hp) p (isNilpotent_mk_envelopeCompletion E p hp)
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp) (envelopeCompletionSigmaNeg E p hp)
    (fun i ↦ ⟨envelopeCompletionXi E p hp i, envelopeCompletionXi_mem E p hp i⟩)

/-- **The inverse of `α`**: the divided power morphism with `x_i ↦ x_i + ξ_i` and
`ξ_i ↦ ξ_i`. -/
public def envelopeCompletionAlphaInv :
    DPMorphism (envelopeCompletionVariableRing E p hp).dividedPowers
      (envelopeCompletionVariableRing E p hp).dividedPowers :=
  completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
    (envelopeCompletionVariableRing E p hp) p (isNilpotent_mk_envelopeCompletion E p hp)
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp) (envelopeCompletionSigma E p hp)
    (fun i ↦ ⟨envelopeCompletionXi E p hp i, envelopeCompletionXi_mem E p hp i⟩)

/-- `α ∘ ν = σ⁻`: on the coefficient ring `D`, `α` is `σ⁻`. -/
public theorem envelopeCompletionAlpha_comp_nu :
    (envelopeCompletionAlpha E p hp).comp (envelopeCompletionNu E p hp) =
      envelopeCompletionSigmaNeg E p hp :=
  completedSetIndexedDividedPowerPolynomialLift_comp_coefficient (envelopeCompletion E p hp) ι
      _ p _ _ _ _

/-- `α(ξ_i) = ξ_i`. -/
public theorem envelopeCompletionAlpha_xi (i : ι) :
    envelopeCompletionAlpha E p hp (envelopeCompletionXi E p hp i) =
        envelopeCompletionXi E p hp i :=
  completedSetIndexedDividedPowerPolynomialLift_variable (envelopeCompletion E p hp) ι _ p _ _ _ _ i

/-- `α⁻¹ ∘ ν = σ`. -/
public theorem envelopeCompletionAlphaInv_comp_nu :
    (envelopeCompletionAlphaInv E p hp).comp (envelopeCompletionNu E p hp) =
      envelopeCompletionSigma E p hp :=
  completedSetIndexedDividedPowerPolynomialLift_comp_coefficient (envelopeCompletion E p hp) ι
      _ p _ _ _ _

/-- `α⁻¹(ξ_i) = ξ_i`. -/
public theorem envelopeCompletionAlphaInv_xi (i : ι) :
    envelopeCompletionAlphaInv E p hp (envelopeCompletionXi E p hp i) =
        envelopeCompletionXi E p hp i :=
  completedSetIndexedDividedPowerPolynomialLift_variable (envelopeCompletion E p hp) ι _ p _ _ _ _ i

/-! ### `α ∘ σ = ν` and `α⁻¹ ∘ σ⁻ = ν` -/

/-- **`α ∘ σ = ν`.** -/
public theorem envelopeCompletionAlpha_comp_sigma :
    (envelopeCompletionAlpha E p hp).comp (envelopeCompletionSigma E p hp) =
      envelopeCompletionNu E p hp := by
  refine eq_of_apply_structureMap_of_apply_coord E p hp _
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp) _ _ (fun x ↦ ?_) (fun i ↦ ?_)
  · exact (congrArg (envelopeCompletionAlpha E p hp)
      (DFunLike.congr_fun (envelopeCompletionSigma_comp_structureMap E p hp) x)).trans
      ((DFunLike.congr_fun (envelopeCompletionAlpha_comp_nu E p hp) _).trans
        (DFunLike.congr_fun (envelopeCompletionSigmaNeg_comp_structureMap E p hp) x))
  · change envelopeCompletionAlpha E p hp (envelopeCompletionSigma E p hp
      (envelopeCompletionCoord E p hp i)) = _
    rw [envelopeCompletionSigma_coord, dPMorphism_map_add, envelopeCompletionAlpha_xi,
      show envelopeCompletionAlpha E p hp (envelopeCompletionNu E p hp
          (envelopeCompletionCoord E p hp i)) =
        envelopeCompletionSigmaNeg E p hp (envelopeCompletionCoord E p hp i) from
        DFunLike.congr_fun (envelopeCompletionAlpha_comp_nu E p hp) _,
      envelopeCompletionSigmaNeg_coord]
    ring

/-- **`α⁻¹ ∘ σ⁻ = ν`**, the mirror of `Crystalline.envelopeCompletionAlpha_comp_sigma`. -/
public theorem envelopeCompletionAlphaInv_comp_sigmaNeg :
    (envelopeCompletionAlphaInv E p hp).comp (envelopeCompletionSigmaNeg E p hp) =
      envelopeCompletionNu E p hp := by
  refine eq_of_apply_structureMap_of_apply_coord E p hp _
    (isNilpotent_mk_envelopeCompletionVariableRing E p hp) _ _ (fun x ↦ ?_) (fun i ↦ ?_)
  · exact (congrArg (envelopeCompletionAlphaInv E p hp)
      (DFunLike.congr_fun (envelopeCompletionSigmaNeg_comp_structureMap E p hp) x)).trans
      ((DFunLike.congr_fun (envelopeCompletionAlphaInv_comp_nu E p hp) _).trans
        (DFunLike.congr_fun (envelopeCompletionSigma_comp_structureMap E p hp) x))
  · change envelopeCompletionAlphaInv E p hp (envelopeCompletionSigmaNeg E p hp
      (envelopeCompletionCoord E p hp i)) = _
    rw [envelopeCompletionSigmaNeg_coord, dPMorphism_map_sub, envelopeCompletionAlphaInv_xi,
      show envelopeCompletionAlphaInv E p hp (envelopeCompletionNu E p hp
          (envelopeCompletionCoord E p hp i)) =
        envelopeCompletionSigma E p hp (envelopeCompletionCoord E p hp i) from
        DFunLike.congr_fun (envelopeCompletionAlphaInv_comp_nu E p hp) _,
      envelopeCompletionSigma_coord]
    ring

/-! ### `α` is an automorphism -/

private theorem envelopeCompletionIdentity_eq_lift :
    DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers =
      completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
        (envelopeCompletionVariableRing E p hp) p (isNilpotent_mk_envelopeCompletion E p hp)
        (isNilpotent_mk_envelopeCompletionVariableRing E p hp) (envelopeCompletionNu E p hp)
        (fun i ↦ ⟨envelopeCompletionXi E p hp i, envelopeCompletionXi_mem E p hp
            i⟩) :=
  eq_completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι _ p _ _ _ _ _
    (dPMorphism_id_comp (envelopeCompletionNu E p hp)) (fun _ ↦ rfl)

/-- **`α ∘ α⁻¹ = id`.** -/
public theorem envelopeCompletionAlpha_comp_alphaInv :
    (envelopeCompletionAlpha E p hp).comp (envelopeCompletionAlphaInv E p hp) =
      DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers := by
  refine Eq.trans (eq_completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
      _ p _ _ _ _ _ ?_ ?_)
    (envelopeCompletionIdentity_eq_lift E p hp).symm
  · apply DPMorphism.ext
    funext x
    exact (congrArg (envelopeCompletionAlpha E p hp)
      (DFunLike.congr_fun (envelopeCompletionAlphaInv_comp_nu E p hp) x)).trans
      (DFunLike.congr_fun (envelopeCompletionAlpha_comp_sigma E p hp) x)
  · intro i
    change envelopeCompletionAlpha E p hp (envelopeCompletionAlphaInv E p hp
      (envelopeCompletionXi E p hp i)) = _
    rw [envelopeCompletionAlphaInv_xi, envelopeCompletionAlpha_xi]

/-- **`α⁻¹ ∘ α = id`.** -/
public theorem envelopeCompletionAlphaInv_comp_alpha :
    (envelopeCompletionAlphaInv E p hp).comp (envelopeCompletionAlpha E p hp) =
      DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers := by
  refine Eq.trans (eq_completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
      _ p _ _ _ _ _ ?_ ?_)
    (envelopeCompletionIdentity_eq_lift E p hp).symm
  · apply DPMorphism.ext
    funext x
    exact (congrArg (envelopeCompletionAlphaInv E p hp)
      (DFunLike.congr_fun (envelopeCompletionAlpha_comp_nu E p hp) x)).trans
      (DFunLike.congr_fun (envelopeCompletionAlphaInv_comp_sigmaNeg E p hp) x)
  · intro i
    change envelopeCompletionAlphaInv E p hp (envelopeCompletionAlpha E p hp
      (envelopeCompletionXi E p hp i)) = _
    rw [envelopeCompletionAlpha_xi, envelopeCompletionAlphaInv_xi]

/-! ### `τ` and the factorization `ρ = τ ∘ σ` -/

variable (rho : DPMorphism (envelopeCompletion E p hp).dividedPowers
    (envelopeCompletion E p hp).dividedPowers)
  (hrhoA : rho.comp (envelopeCompletionStructureMap E p hp) =
      envelopeCompletionStructureMap E p hp)
  (hrhoaug : IsAugmentationCompatible rho)

/-- **`τ : D⟨ξ_i⟩^∧ → D`**, the divided power `D`-algebra map sending `ξ_i` to
`z_i = ρ(x_i) - x_i`. -/
public def envelopeCompletionTau :
    DPMorphism (envelopeCompletionVariableRing E p hp).dividedPowers
        (envelopeCompletion E p hp).dividedPowers :=
  completedSetIndexedDividedPowerPolynomialLift (envelopeCompletion E p hp) ι
      (envelopeCompletion E p hp) p
    (isNilpotent_mk_envelopeCompletion E p hp) (isNilpotent_mk_envelopeCompletion E p hp)
    (DPMorphism.id (envelopeCompletion E p hp).dividedPowers)
    (fun i ↦ ⟨rho (envelopeCompletionCoord E p hp i) - envelopeCompletionCoord E p hp i,
      hrhoaug (envelopeCompletionCoord E p hp i)⟩)

/-- **`τ ∘ ν = id_D`**: the structure map `ν` is a section of `τ`. -/
public theorem envelopeCompletionTau_comp_nu :
    (envelopeCompletionTau E p hp rho hrhoaug).comp (envelopeCompletionNu E p hp) =
      DPMorphism.id (envelopeCompletion E p hp).dividedPowers :=
  completedSetIndexedDividedPowerPolynomialLift_comp_coefficient (envelopeCompletion E p hp) ι
      _ p _ _ _ _

/-- `τ(ξ_i) = z_i = ρ(x_i) - x_i`. -/
public theorem envelopeCompletionTau_xi (i : ι) :
    envelopeCompletionTau E p hp rho hrhoaug (envelopeCompletionXi E p hp i) =
      rho (envelopeCompletionCoord E p hp i) - envelopeCompletionCoord E p hp i :=
  completedSetIndexedDividedPowerPolynomialLift_variable (envelopeCompletion E p hp) ι _ p _ _ _ _ i

include hrhoA in
/-- **The factorization `ρ = τ ∘ σ`**. -/
public theorem envelopeCompletionTau_comp_sigma :
    (envelopeCompletionTau E p hp rho hrhoaug).comp (envelopeCompletionSigma E p hp) = rho := by
  refine eq_of_apply_structureMap_of_apply_coord E p hp _
    (isNilpotent_mk_envelopeCompletion E p hp) _ _ (fun x ↦ ?_) (fun i ↦ ?_)
  · exact (congrArg (envelopeCompletionTau E p hp rho hrhoaug)
      (DFunLike.congr_fun (envelopeCompletionSigma_comp_structureMap E p hp) x)).trans
      ((DFunLike.congr_fun (envelopeCompletionTau_comp_nu E p hp rho hrhoaug) _).trans
        (DFunLike.congr_fun hrhoA x).symm)
  · change envelopeCompletionTau E p hp rho hrhoaug (envelopeCompletionSigma E p hp
      (envelopeCompletionCoord E p hp i)) = _
    rw [envelopeCompletionSigma_coord, dPMorphism_map_add, envelopeCompletionTau_xi,
      show envelopeCompletionTau E p hp rho hrhoaug (envelopeCompletionNu E p hp
          (envelopeCompletionCoord E p hp i)) = envelopeCompletionCoord E p hp i from
        DFunLike.congr_fun (envelopeCompletionTau_comp_nu E p hp rho hrhoaug) _]
    ring

include hrhoA hrhoaug in
/-- **The factorization of `ρ`, in one statement.**

For any divided power `A`-algebra endomorphism `ρ` of `D` compatible with the augmentation there
are divided power morphisms `σ : D → D⟨ξ_i⟩^∧`, `τ : D⟨ξ_i⟩^∧ → D` and mutually inverse
`α, α⁻¹ : D⟨ξ_i⟩^∧ → D⟨ξ_i⟩^∧` with

* `τ ∘ σ = ρ` — the factorization of `ρ`;
* `α ∘ σ = ν` — so `α ∘ σ` is the structure map;
* `τ ∘ ν = id_D` — so `ν` is a section of `τ`;

together with the values `σ(x_i) = x_i + ξ_i`, `τ(ξ_i) = ρ(x_i) - x_i`, `α(x_i) = x_i - ξ_i` and
`α(ξ_i) = ξ_i`. -/
public theorem exists_factorization_of_isAugmentationCompatible :
    ∃ (sig : DPMorphism (envelopeCompletion E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers)
      (tau : DPMorphism (envelopeCompletionVariableRing E p hp).dividedPowers
          (envelopeCompletion E p hp).dividedPowers)
      (alp alpInv : DPMorphism (envelopeCompletionVariableRing E p hp).dividedPowers
        (envelopeCompletionVariableRing E p hp).dividedPowers),
      tau.comp sig = rho ∧
        alp.comp sig = envelopeCompletionNu E p hp ∧
        tau.comp (envelopeCompletionNu E p hp) = DPMorphism.id
            (envelopeCompletion E p hp).dividedPowers ∧
        alp.comp alpInv = DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers ∧
        alpInv.comp alp = DPMorphism.id (envelopeCompletionVariableRing E p hp).dividedPowers ∧
        (∀ i : ι, sig (envelopeCompletionCoord E p hp i) =
          envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) +
              envelopeCompletionXi E p hp i) ∧
        (∀ i : ι, tau (envelopeCompletionXi E p hp i) =
          rho (envelopeCompletionCoord E p hp i) - envelopeCompletionCoord E p hp
              i) ∧
        (∀ i : ι, alp (envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i)) =
          envelopeCompletionNu E p hp (envelopeCompletionCoord E p hp i) -
            envelopeCompletionXi E p hp i) ∧
        (∀ i : ι, alp (envelopeCompletionXi E p hp i) = envelopeCompletionXi E p hp i) :=
  ⟨envelopeCompletionSigma E p hp, envelopeCompletionTau E p hp rho hrhoaug,
    envelopeCompletionAlpha E p hp, envelopeCompletionAlphaInv E p hp,
    envelopeCompletionTau_comp_sigma E p hp rho hrhoA hrhoaug,
    envelopeCompletionAlpha_comp_sigma E p hp,
    envelopeCompletionTau_comp_nu E p hp rho hrhoaug,
    envelopeCompletionAlpha_comp_alphaInv E p hp,
    envelopeCompletionAlphaInv_comp_alpha E p hp,
    envelopeCompletionSigma_coord E p hp,
    envelopeCompletionTau_xi E p hp rho hrhoaug,
    fun i ↦ (DFunLike.congr_fun (envelopeCompletionAlpha_comp_nu E p hp) _).trans
      (envelopeCompletionSigmaNeg_coord E p hp i),
    envelopeCompletionAlpha_xi E p hp⟩

end Instances

end Factorization

end Crystalline

end
