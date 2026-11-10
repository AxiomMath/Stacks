module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality

/-!
# The cosimplicial envelope of a polynomial presentation

Work in an affine crystalline situation `(A, I, γ)` with target `C`, choose a polynomial algebra
`P = A[x_i]` over `A` and a surjection `P → C`.  This file constructs a term of
`Crystalline.CosimplicialEnvelope`, the structure which records the cosimplicial ring `D(*)` of
`p`-adically completed divided power envelopes of the kernels `J(n)` of the surjections
`P ⊗_A ⋯ ⊗_A P → C` together with the cosimplicial module `Ω_{D(*)}` of `p`-adically completed
divided power differentials over it.

## What is and is not proved

Proved: the structure is inhabited for every affine crystalline situation and every surjective
polynomial presentation of its target, carrying no hypotheses beyond the ones the structure's own
arguments mention.  Every field is discharged, so `D(*)` is a genuine cosimplicial ring whose
degree `n` is the completed divided power envelope of `J(n)` and whose structure maps are the
completions of the divided power morphisms reindexing the variables, and `Ω_{D(*)}` is a genuine
cosimplicial module over it whose structure maps are semilinear, adically continuous and
compatible with the universal derivations.

Not proved here: nothing about the crystalline site, and nothing identifying a cosimplicial
module of sections of a sheaf with `M_* ⊗̂_{D(*)} Ω^i_{D(*)}`.  This file makes the statements
which quantify over `Crystalline.CosimplicialEnvelope` — Tags 07L9 and 07LA — apply to a concrete
situation instead of being vacuous; it does not apply them.

## Main definitions

* `Crystalline.polynomialEnvelopeMap` — functoriality of the divided power envelope of a
  polynomial presentation of `C` in the presentation.
* `Crystalline.envelopeReindex` — the divided power morphism `D(n)_env → D(m)_env` induced by a
  map of finite ordinals, before completion.
* `Crystalline.cosimplicialEnvelopeRing` — the cosimplicial ring `D(0) → D(1) → D(2) → ⋯`.
* `Crystalline.cosimplicialEnvelopeDifferentials` — the cosimplicial module `Ω_{D(*)}` over it.
* `Crystalline.cosimplicialEnvelope` — the resulting term of `Crystalline.CosimplicialEnvelope`.

## Main results

* `Crystalline.cosimplicialEnvelope_differentials_homotopic_zero` and
  `Crystalline.cosimplicialEnvelope_completedForms_homotopic_zero` — Tags 07L9 and 07LA read on
  the constructed envelope, so that neither statement is vacuous.

* `Crystalline.adicCompletionRingMap_isDPMorphism` — the ring map induced on `p`-adic completions
  by a divided power morphism is a divided power morphism for the completed divided powers.
* `Crystalline.envelopeReindex_id` and `Crystalline.envelopeReindex_comp` — the reindexing
  morphisms are functorial, by the uniqueness half of the universal property of the envelope.

## Implementation notes

The cosimplicial structure maps are *not* obtained from the coproduct description of `D(n)` of
Tag 07L4, which is `Crystalline.completedEnvelope_isCoproduct`.  They are obtained from the
universal property of the divided power envelope of a polynomial presentation: a renaming of the
variables `x_i(e) ↦ x_i(φ(e))` commuting with the two maps to `C` is a morphism of the two
ring--ideal pairs, so it induces a divided power morphism of the envelopes, and the cosimplicial
identities follow from the uniqueness half of the same universal property.  The structure
`Crystalline.CosimplicialEnvelope` demands that its structure maps agree with those renamings on
the image of the polynomial algebra, so building them this way makes that field hold by
construction; the coproduct description would instead have to be compared with the renamings on
the variables first, and the comparison is not available.

The cosimplicial module `Ω_{D(*)}` is assembled as semilinear data and then read as a presheaf of
modules by `Crystalline.SemilinearCosimplicialModule.toCosimplicialModule`.  Its transition maps
are the completions of the maps induced on divided power differentials by the reindexing divided
power morphisms; that is what makes the compatibility with the universal derivations a statement
about the dense image of the uncompleted differentials, where it is the compatibility of the
induced map with the uncompleted universal differential.

No declaration here carries a tag: the rings `D(n)` and the modules `Ω_{D(n)}` are the notation
of the equations (07JF) and (07L0), which assert nothing, and the tags of the propositions about
them — 07L4, 07L9, 07LA — are already placed where those are proved.

## References

* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Equation 60.21.1, Tag 07L0](https://stacks.math.columbia.edu/tag/07L0)
* [Stacks Project, Lemma 60.21.1, Tag 07L9](https://stacks.math.columbia.edu/tag/07L9)
* [Stacks Project, Lemma 60.21.2, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite Simplicial

universe u v w

namespace Crystalline

/-! ### Ring maps and divided powers on adic completions -/

section CompletionRingMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism read as a semilinear map of the two rings viewed as modules over
themselves. -/
public def ringHomₛₗ (σ : R →+* S) : R →ₛₗ[σ] S where
  __ := σ.toAddMonoidHom
  map_smul' := σ.map_mul

/-- The ring homomorphism induced on adic completions by a ring homomorphism which carries the
one adic ideal into the other.  On underlying additive groups it is
`Crystalline.adicCompletionMapₛₗ`. -/
public noncomputable def adicCompletionRingMap (σ : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map σ ≤ J) : AdicCompletion I R →+* AdicCompletion J S where
  __ := (adicCompletionMapₛₗ (ringHomₛₗ σ) h).toAddMonoidHom
  map_one' := by
    ext n
    change Submodule.Quotient.mk (σ 1) = (1 : S ⧸ J ^ n • (⊤ : Ideal S))
    rw [map_one]
    rfl
  map_mul' x y := by
    ext n
    change adicQuotientMap (ringHomₛₗ σ) h n (x.val n * y.val n) =
      adicQuotientMap (ringHomₛₗ σ) h n (x.val n) * adicQuotientMap (ringHomₛₗ σ) h n (y.val n)
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (x.val n)
    obtain ⟨b, hb⟩ := Submodule.mkQ_surjective _ (y.val n)
    rw [← ha, ← hb]
    change Submodule.Quotient.mk (σ (a * b)) =
      (Submodule.Quotient.mk (σ a * σ b) : S ⧸ J ^ n • (⊤ : Ideal S))
    rw [map_mul]

/-- The induced ring map on completions agrees with the original one on the canonical image of
the uncompleted ring. -/
public lemma adicCompletionRingMap_of (σ : R →+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map σ ≤ J) (x : R) :
    adicCompletionRingMap σ h (AdicCompletion.of I R x) = AdicCompletion.of J S (σ x) :=
  adicCompletionMapₛₗ_of (ringHomₛₗ σ) h x

/-- The completion of a semilinear map is semilinear over the induced map of the completed
scalars. -/
public lemma adicCompletionMapₛₗ_smul {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module S Q] {σ : R →+* S} {I : Ideal R} {J : Ideal S}
    (g : P →ₛₗ[σ] Q) (h : I.map σ ≤ J) (r : AdicCompletion I R) (x : AdicCompletion I P) :
    adicCompletionMapₛₗ g h (r • x) =
      adicCompletionRingMap σ h r • adicCompletionMapₛₗ g h x := by
  apply AdicCompletion.ext
  intro n
  change adicQuotientMap g h n (r.val n • x.val n) =
    adicQuotientMap (ringHomₛₗ σ) h n (r.val n) • adicQuotientMap g h n (x.val n)
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective _ (r.val n)
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective _ (x.val n)
  rw [← ha, ← hb]
  change Submodule.Quotient.mk (g (a • b)) =
    (Submodule.Quotient.mk (σ a • g b) : Q ⧸ J ^ n • (⊤ : Submodule S Q))
  rw [g.map_smulₛₗ]

/-- Every ring homomorphism carries the ideal generated by `p` into the ideal generated by
`p`. -/
public lemma map_pAdicIdeal_le (p : ℕ) (σ : R →+* S) :
    (DividedPowers.pAdicIdeal (A := R) p).map σ ≤ DividedPowers.pAdicIdeal (A := S) p := by
  simp [DividedPowers.pAdicIdeal, Ideal.map_span, Set.image_singleton]

/-- A ring homomorphism carrying one distinguished ideal into the other, read as a semilinear map
of those ideals. -/
public def idealMapₛₗ {I : Ideal R} {J : Ideal S} (σ : R →+* S) (h : I.map σ ≤ J) :
    I →ₛₗ[σ] J where
  toFun x := ⟨σ x, h (Ideal.mem_map_of_mem σ x.property)⟩
  map_add' x y := Subtype.ext (map_add σ (x : R) (y : R))
  map_smul' r x := Subtype.ext (map_mul σ r (x : R))

/-- The image of an adic Cauchy sequence under a semilinear map which carries the one adic ideal
into the other. -/
public def adicCauchySequenceMapₛₗ {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module S Q] {σ : R →+* S} (g : P →ₛₗ[σ] Q) {I : Ideal R} {J : Ideal S}
    (h : I.map σ ≤ J) (c : AdicCompletion.AdicCauchySequence I P) :
    AdicCompletion.AdicCauchySequence J Q :=
  ⟨fun n => g (c n), by
    intro m n hmn
    rw [SModEq.sub_mem, ← map_sub]
    exact pow_smul_top_le_comap g h m ((SModEq.sub_mem).mp (c.property hmn))⟩

/-- The induced ring map on completions takes the class of a Cauchy sequence of elements of the
distinguished ideal to the class of its image. -/
private lemma adicCompletionRingMap_idealSequence {I : Ideal R} {J : Ideal S}
    (p : ℕ) (σ : R →+* S) (h : I.map σ ≤ J)
    (c : AdicCompletion.AdicCauchySequence (DividedPowers.pAdicIdeal (A := R) p) I) :
    adicCompletionRingMap σ (map_pAdicIdeal_le p σ)
      (AdicCompletion.map (DividedPowers.pAdicIdeal p) I.subtype
        (AdicCompletion.mk (DividedPowers.pAdicIdeal p) I c)) =
      AdicCompletion.map (DividedPowers.pAdicIdeal p) J.subtype
        (AdicCompletion.mk (DividedPowers.pAdicIdeal p) J
          (adicCauchySequenceMapₛₗ (idealMapₛₗ σ h) (map_pAdicIdeal_le p σ) c)) := by
  apply AdicCompletion.ext
  intro n
  rfl

/-- **The completion of a divided power morphism is a divided power morphism.**  For divided
power ideals whose divided powers extend to the completions, the ring map induced on the `p`-adic
completions by a divided power morphism preserves the extended divided powers: both sides are
computed on a Cauchy sequence of representatives inside the ideal, where the statement is the
original compatibility. -/
public lemma adicCompletionRingMap_isDPMorphism {I : Ideal R} {J : Ideal S}
    (δ : DividedPowers I) (ε : DividedPowers J) (p : ℕ)
    (hR : IsNilpotent (Ideal.Quotient.mk I (p : R)))
    (hS : IsNilpotent (Ideal.Quotient.mk J (p : S)))
    (σ : DividedPowers.DPMorphism δ ε) :
    DividedPowers.IsDPMorphism (DividedPowers.completedDividedPowers I δ p hR).1
      (DividedPowers.completedDividedPowers J ε p hS).1
      (adicCompletionRingMap σ.toRingHom (map_pAdicIdeal_le p σ.toRingHom)) := by
  have hc : ∀ (x) (hx : x ∈ DividedPowers.completionIdeal I p hR),
      AdicCompletion.map (DividedPowers.pAdicIdeal p) I.subtype
      (AdicCompletion.mk (DividedPowers.pAdicIdeal p) I
        (DividedPowers.completionIdealRepSequence I p hR ⟨x, hx⟩)) = x := fun x hx =>
    DividedPowers.completionIdealRepSequence_map_eq I p hR ⟨x, hx⟩
  constructor
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change adicCompletionRingMap σ.toRingHom _ x ∈ DividedPowers.completionIdeal J p hS
    rw [← hc x hx, adicCompletionRingMap_idealSequence p σ.toRingHom σ.ideal_comp]
    exact DividedPowers.completion_map_subtype_mem J p hS _
  · intro n x hx
    change DividedPowers.completedDpowAux J ε p hS n (adicCompletionRingMap σ.toRingHom _ x) =
      adicCompletionRingMap σ.toRingHom _ (DividedPowers.completedDpowAux I δ p hR n x)
    rw [← hc x hx, adicCompletionRingMap_idealSequence p σ.toRingHom σ.ideal_comp,
      DividedPowers.completedDpowAux_of_rep, DividedPowers.completedDpowAux_of_rep]
    apply AdicCompletion.ext
    intro k
    change (DividedPowers.pAdicIdeal (A := S) p ^ k • (⊤ : Ideal S)).mkQ
        (ε.dpow n (σ (DividedPowers.completionIdealRepSequence I p hR ⟨x, hx⟩ k))) =
      (DividedPowers.pAdicIdeal (A := S) p ^ k • (⊤ : Ideal S)).mkQ
        (σ (δ.dpow n (DividedPowers.completionIdealRepSequence I p hR ⟨x, hx⟩ k)))
    exact congrArg (DividedPowers.pAdicIdeal (A := S) p ^ k • (⊤ : Ideal S)).mkQ
      (σ.dpow_comp (n := n) _
        (DividedPowers.completionIdealRepSequence I p hR ⟨x, hx⟩ k).property)

/-- **Every additive map between `p`-adic completions is adically continuous**, because the
`n`-th stage of the `p`-adic filtration is `p ^ n` times the completion and an additive map
commutes with multiplication by the natural number `p ^ n`. -/
public lemma pAdicIdeal_adicContinuous {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module S Q] (p : ℕ)
    (F : AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) P →+
      AdicCompletion (DividedPowers.pAdicIdeal (A := S) p) Q) :
    SemilinearCosimplicialModule.AdicContinuous (DividedPowers.pAdicIdeal (A := R) p)
      (DividedPowers.pAdicIdeal (A := S) p) F := by
  intro n
  refine ⟨n, fun x hx => ?_⟩
  have hx' : x ∈ DividedPowers.pAdicIdeal (A := R) p ^ n •
      (⊤ : Submodule R (AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) P)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _)]
    exact hx
  change x ∈ Ideal.span {(p : R)} ^ n •
    (⊤ : Submodule R (AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) P)) at hx'
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hx'
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx'
  have hF : F ((p : R) ^ n • y) = (p : S) ^ n • F y := by
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [← hy, hF]
  apply AdicCompletion.pow_smul_top_le_ker_eval _ n
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n) Submodule.mem_top

end CompletionRingMap

/-! ### Functoriality of the envelope of a polynomial presentation -/

section Reindex

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The distinguished divided power ideal of the base maps into the kernel of a polynomial
presentation of `C`, because it maps to zero in `C`. -/
public lemma ideal_map_le_ker_presentation :
    s.A.ideal.map (algebraMap s.A (MvPolynomial ι s.A)) ≤ RingHom.ker f.toRingHom := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f (algebraMap s.A (MvPolynomial ι s.A) x) = 0
  rw [f.commutes]
  have hx' : algebraMap s.A s.C x ∈ s.A.ideal.map (algebraMap s.A s.C) :=
    Ideal.mem_map_of_mem (algebraMap s.A s.C) hx
  rwa [s.ideal_map_eq_bot] at hx'

/-- A renaming of the variables commuting with the two presentations of `C` is a morphism of the
kernels of those presentations, read as ring--ideal pairs. -/
public noncomputable def renameKerHom {κ : Type w} (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (r : MvPolynomial ι s.A →ₐ[s.A] MvPolynomial κ s.A) (hr : g.comp r = f) :
    IdealPair.Hom (RingHom.ker f.toRingHom) (RingHom.ker g.toRingHom) :=
  IdealPair.Hom.ofRingHom r.toRingHom (by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g (r x) = 0
    simpa only [← AlgHom.comp_apply, hr] using (show f x = 0 from hx))

/-- The datum which the universal property of the envelope of the first presentation turns into
a divided power morphism of envelopes: the map to the envelope of the second presentation,
composed with the renaming of the variables. -/
public noncomputable def renameEnvelopeHomOver {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (r : MvPolynomial ι s.A →ₐ[s.A] MvPolynomial κ s.A) (hr : g.comp r = f) :
    IdealPair.HomOver
      (IdealPair.Hom.ofRingHom (algebraMap s.A (MvPolynomial ι s.A))
        (ideal_map_le_ker_presentation s f))
      (IdealPair.Hom.ofDPMorphism (polynomialDividedPowerEnvelope s g).structureMap) :=
  ⟨IdealPair.Hom.comp (polynomialDividedPowerEnvelope s g).algebraMap
      (renameKerHom s f g r hr), by
    apply IdealPair.Hom.ext_toRingHom
    apply RingHom.ext
    intro a
    change (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom
        (r (algebraMap s.A (MvPolynomial ι s.A) a)) =
      (polynomialDividedPowerEnvelope s g).structureMap.toRingHom a
    rw [r.commutes]
    exact RingHom.congr_fun (polynomialDividedPowerEnvelope s g).algebraMap_comp a⟩

/-- **Functoriality of the divided power envelope of a polynomial presentation.**  A renaming of
the variables commuting with the two presentations of `C` induces a divided power morphism of the
envelopes over the base, by the universal property of the envelope of the first presentation. -/
public noncomputable def polynomialEnvelopeMap {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (r : MvPolynomial ι s.A →ₐ[s.A] MvPolynomial κ s.A) (hr : g.comp r = f) :
    {q : DividedPowers.DPMorphism
        (polynomialDividedPowerEnvelope s f).object.dividedPowers
        (polynomialDividedPowerEnvelope s g).object.dividedPowers //
      q.comp (polynomialDividedPowerEnvelope s f).structureMap =
        (polynomialDividedPowerEnvelope s g).structureMap} :=
  ((polynomialDividedPowerEnvelope s f).homEquiv (polynomialDividedPowerEnvelope s g).object
    (polynomialDividedPowerEnvelope s g).structureMap).symm (renameEnvelopeHomOver s f g r hr)

/-- The induced divided power morphism of envelopes agrees with the renaming of the variables on
the image of the polynomial algebra. -/
public lemma polynomialEnvelopeMap_polynomial {κ : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (r : MvPolynomial ι s.A →ₐ[s.A] MvPolynomial κ s.A) (hr : g.comp r = f)
    (x : MvPolynomial ι s.A) :
    (polynomialEnvelopeMap s f g r hr).1
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x) =
      (polynomialDividedPowerEnvelope s g).algebraMap.toRingHom (r x) := by
  have hsymm := ((polynomialDividedPowerEnvelope s f).homEquiv
    (polynomialDividedPowerEnvelope s g).object
    (polynomialDividedPowerEnvelope s g).structureMap).apply_symm_apply
      (renameEnvelopeHomOver s f g r hr)
  have happly := (polynomialDividedPowerEnvelope s f).homEquiv_apply
    (polynomialDividedPowerEnvelope s g).object
    (polynomialDividedPowerEnvelope s g).structureMap (polynomialEnvelopeMap s f g r hr)
  have hcomp : IdealPair.Hom.comp
      (IdealPair.Hom.ofDPMorphism (polynomialEnvelopeMap s f g r hr).1)
      (polynomialDividedPowerEnvelope s f).algebraMap =
      IdealPair.Hom.comp (polynomialDividedPowerEnvelope s g).algebraMap
        (renameKerHom s f g r hr) :=
    happly.symm.trans (congrArg Subtype.val hsymm)
  exact congrArg (fun z : IdealPair.Hom _ _ => z.toRingHom x) hcomp

/-- A divided power morphism out of the envelope of a polynomial presentation is determined by
its values on the image of the polynomial algebra, among those compatible with the base. -/
public lemma polynomialEnvelopeMap_ext {κ : Type w} (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (a b : DividedPowers.DPMorphism
      (polynomialDividedPowerEnvelope s f).object.dividedPowers
      (polynomialDividedPowerEnvelope s g).object.dividedPowers)
    (ha : a.comp (polynomialDividedPowerEnvelope s f).structureMap =
      (polynomialDividedPowerEnvelope s g).structureMap)
    (hb : b.comp (polynomialDividedPowerEnvelope s f).structureMap =
      (polynomialDividedPowerEnvelope s g).structureMap)
    (hab : ∀ x, a ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x) =
      b ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x)) : a = b := by
  suffices h : (polynomialDividedPowerEnvelope s f).homEquiv
        (polynomialDividedPowerEnvelope s g).object
        (polynomialDividedPowerEnvelope s g).structureMap ⟨a, ha⟩ =
      (polynomialDividedPowerEnvelope s f).homEquiv
        (polynomialDividedPowerEnvelope s g).object
        (polynomialDividedPowerEnvelope s g).structureMap ⟨b, hb⟩ from
    congrArg Subtype.val (((polynomialDividedPowerEnvelope s f).homEquiv
      (polynomialDividedPowerEnvelope s g).object
      (polynomialDividedPowerEnvelope s g).structureMap).injective h)
  apply Subtype.ext
  rw [(polynomialDividedPowerEnvelope s f).homEquiv_apply,
    (polynomialDividedPowerEnvelope s f).homEquiv_apply]
  apply IdealPair.Hom.ext_toRingHom
  apply RingHom.ext
  exact hab

/-- The reindexing of the variables of the `(n + 1)`-fold tensor power induced by a map of finite
ordinals, for arbitrary objects of the simplex category. -/
public def simplexVariableMap {n m : SimplexCategory} (φ : n ⟶ m) :
    Fin (n.len + 1) × ι → Fin (m.len + 1) × ι :=
  fun q ↦ (φ.toOrderHom q.1, q.2)

/-- **The reindexing divided power morphism `D(n)_env → D(m)_env`.**  A map of finite ordinals
`φ : n ⟶ m` renames the variable `x_i(e)` of the `(n + 1)`-fold tensor power to the variable
`x_i(φ(e))` of the `(m + 1)`-fold tensor power; this commutes with the two surjections onto `C`,
so it induces a divided power morphism of the divided power envelopes of their kernels. -/
public noncomputable def envelopeReindex {n m : SimplexCategory} (φ : n ⟶ m) :
    {q : DividedPowers.DPMorphism (tensorPowerEnvelope s f n.len).object.dividedPowers
        (tensorPowerEnvelope s f m.len).object.dividedPowers //
      q.comp (tensorPowerEnvelope s f n.len).structureMap =
        (tensorPowerEnvelope s f m.len).structureMap} :=
  polynomialEnvelopeMap s (tensorPowerPresentation s f n.len)
    (tensorPowerPresentation s f m.len)
    (MvPolynomial.rename (simplexVariableMap (ι := ι) φ)) (by
      ext x
      simp [tensorPowerPresentation, simplexVariableMap])

/-- The reindexing morphism renames the variables on the image of the polynomial algebra. -/
public lemma envelopeReindex_polynomial {n m : SimplexCategory} (φ : n ⟶ m)
    (x : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    (envelopeReindex s f φ).1 ((tensorPowerEnvelope s f n.len).algebraMap.toRingHom x) =
      (tensorPowerEnvelope s f m.len).algebraMap.toRingHom
        (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) x) :=
  polynomialEnvelopeMap_polynomial s _ _ _ _ x

/-- The reindexing morphism along an identity is the identity. -/
public lemma envelopeReindex_id (n : SimplexCategory)
    (x : (tensorPowerEnvelope s f n.len).object) :
    (envelopeReindex s f (𝟙 n)).1 x = x := by
  have h : (envelopeReindex s f (𝟙 n)).1 =
      DividedPowers.DPMorphism.id (tensorPowerEnvelope s f n.len).object.dividedPowers := by
    apply polynomialEnvelopeMap_ext s (tensorPowerPresentation s f n.len)
      (tensorPowerPresentation s f n.len)
    · exact (envelopeReindex s f (𝟙 n)).2
    · ext a
      rfl
    · intro a
      rw [envelopeReindex_polynomial]
      have hr : simplexVariableMap (ι := ι) (𝟙 n) = (id : Fin (n.len + 1) × ι → _) := rfl
      rw [hr, MvPolynomial.rename_id]
      rfl
  exact congrArg (fun q => q x) h

/-- The reindexing morphisms compose. -/
public lemma envelopeReindex_comp {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k)
    (x : (tensorPowerEnvelope s f n.len).object) :
    (envelopeReindex s f (φ ≫ ψ)).1 x =
      (envelopeReindex s f ψ).1 ((envelopeReindex s f φ).1 x) := by
  have h : (envelopeReindex s f (φ ≫ ψ)).1 =
      (envelopeReindex s f ψ).1.comp (envelopeReindex s f φ).1 := by
    apply polynomialEnvelopeMap_ext s (tensorPowerPresentation s f n.len)
      (tensorPowerPresentation s f k.len)
    · exact (envelopeReindex s f (φ ≫ ψ)).2
    · have hφ := (envelopeReindex s f φ).2
      have hψ := (envelopeReindex s f ψ).2
      ext a
      exact (congrArg (fun q => (envelopeReindex s f ψ).1 (q a)) hφ).trans
        (congrArg (fun q => q a) hψ)
    · intro a
      change (envelopeReindex s f (φ ≫ ψ)).1 _ =
        (envelopeReindex s f ψ).1 ((envelopeReindex s f φ).1 _)
      rw [envelopeReindex_polynomial, envelopeReindex_polynomial, envelopeReindex_polynomial,
        MvPolynomial.rename_rename]
      rfl
  exact congrArg (fun q => q x) h

end Reindex

/-! ### The cosimplicial ring `D(*)` -/

section CosimplicialRing

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The cosimplicial ring `D(0) → D(1) → D(2) → ⋯`** of `p`-adically completed divided power
envelopes of the kernels of the surjections `P ⊗_A ⋯ ⊗_A P → C`: a map of finite ordinals acts by
the completion of the divided power morphism which reindexes the variables. -/
public noncomputable def cosimplicialEnvelopeRing : CosimplicialObject CommRingCat.{max u w} where
  obj n := CommRingCat.of (pAdicCompletedTensorPowerEnvelope s f hf n.len)
  map φ := CommRingCat.ofHom (adicCompletionRingMap (envelopeReindex s f φ).1.toRingHom
    (map_pAdicIdeal_le s.p _))
  map_id n := by
    ext x
    exact adicCompletionMapₛₗ_id_apply _ _ (envelopeReindex_id s f n) x
  map_comp φ ψ := by
    ext x
    exact adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _ (envelopeReindex_comp s f φ ψ) x

/-- The structure maps of `D(*)` rename the variables on the image of the polynomial algebra. -/
public lemma cosimplicialEnvelopeRing_map_polynomial {n m : SimplexCategory} (φ : n ⟶ m)
    (q : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    (cosimplicialEnvelopeRing s f hf).map φ (tensorPowerEnvelopeMap s f hf n.len q) =
      tensorPowerEnvelopeMap s f hf m.len
        (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) q) := by
  change adicCompletionRingMap (envelopeReindex s f φ).1.toRingHom _
    (AdicCompletion.of _ _ ((tensorPowerEnvelope s f n.len).algebraMap.toRingHom q)) = _
  rw [adicCompletionRingMap_of]
  exact congrArg (AdicCompletion.of _ _) (envelopeReindex_polynomial s f φ q)

/-- The structure maps of `D(*)` are divided power morphisms of the completed divided power
envelopes. -/
public lemma cosimplicialEnvelopeRing_isDPMorphism {n m : SimplexCategory} (φ : n ⟶ m) :
    DividedPowers.IsDPMorphism
      (completedTensorPowerDividedPowerRing s f hf n.len).dividedPowers
      (completedTensorPowerDividedPowerRing s f hf m.len).dividedPowers
      ((cosimplicialEnvelopeRing s f hf).map φ).hom :=
  adicCompletionRingMap_isDPMorphism _ _ s.p
    (completedTensorPowerDifferential s f hf n.len).1
    (completedTensorPowerDifferential s f hf m.len).1
    (envelopeReindex s f φ).1

end CosimplicialRing

/-! ### The cosimplicial module `Ω_{D(*)}` -/

section CosimplicialDifferentials

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The envelope of `J(n)` is an algebra over the base of the situation through its structure
morphism. -/
public noncomputable abbrev tensorPowerEnvelopeAlgebra (n : ℕ) :
    Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
  (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra

attribute [local instance] tensorPowerEnvelopeAlgebra

/-- The module of divided power differentials of the envelope of `J(n)`, of which `Ω_{D(n)}` is
the `p`-adic completion. -/
public noncomputable abbrev envelopeDifferentials (n : ℕ) : Type (max u w) :=
  letI : Algebra (s.A : Type u) (tensorPowerEnvelope s f n).object :=
    (tensorPowerEnvelope s f n).structureMap.toRingHom.toAlgebra
  dividedPowerDifferentials (A := (s.A : Type u))
    (tensorPowerEnvelope s f n).object.dividedPowers

/-- The reindexing divided power morphism of envelopes, read as a morphism of algebras over the
base of the situation. -/
public noncomputable def envelopeReindexAlgHom {n m : SimplexCategory} (φ : n ⟶ m) :
    (tensorPowerEnvelope s f n.len).object →ₐ[(s.A : Type u)]
      (tensorPowerEnvelope s f m.len).object where
  __ := (envelopeReindex s f φ).1.toRingHom
  commutes' a := congrArg (fun q => q a) (envelopeReindex s f φ).2

/-- The map induced on the divided power differentials of the envelopes by the reindexing
morphism, semilinear over it. -/
public noncomputable def envelopeDifferentialsMap {n m : SimplexCategory} (φ : n ⟶ m) :
    envelopeDifferentials s f n.len →ₛₗ[(envelopeReindex s f φ).1.toRingHom]
      envelopeDifferentials s f m.len where
  __ := mapDifferentialsOfDPMorphism
    (J := (tensorPowerEnvelope s f n.len).object.ideal)
    (delta := (tensorPowerEnvelope s f n.len).object.dividedPowers)
    (tensorPowerEnvelope s f m.len).object.dividedPowers (envelopeReindexAlgHom s f φ)
    (envelopeReindex s f φ).1.isDPMorphism
  map_smul' := mapDifferentialsOfDPMorphism_smul
    (J := (tensorPowerEnvelope s f n.len).object.ideal)
    (delta := (tensorPowerEnvelope s f n.len).object.dividedPowers)
    (tensorPowerEnvelope s f m.len).object.dividedPowers (envelopeReindexAlgHom s f φ)
    (envelopeReindex s f φ).1.isDPMorphism

/-- The induced map on divided power differentials takes the universal differential of an element
to the universal differential of its image. -/
public lemma envelopeDifferentialsMap_d {n m : SimplexCategory} (φ : n ⟶ m)
    (x : (tensorPowerEnvelope s f n.len).object) :
    envelopeDifferentialsMap s f φ
        (dividedPowerDifferential (A := (s.A : Type u))
          (tensorPowerEnvelope s f n.len).object.dividedPowers x) =
      dividedPowerDifferential (A := (s.A : Type u))
        (tensorPowerEnvelope s f m.len).object.dividedPowers ((envelopeReindex s f φ).1 x) :=
  mapDifferentialsOfDPMorphism_d (J := _) (delta := _) _ _
    (envelopeReindex s f φ).1.isDPMorphism x

/-- The induced map along an identity is the identity. -/
public lemma envelopeDifferentialsMap_id (n : SimplexCategory)
    (x : envelopeDifferentials s f n.len) :
    envelopeDifferentialsMap s f (𝟙 n) x = x := by
  have h : (envelopeDifferentialsMap s f (𝟙 n)).toAddMonoidHom = AddMonoidHom.id _ := by
    apply differentials_hom_ext _ _ (RingHom.id _)
    · intro r y
      change envelopeDifferentialsMap s f (𝟙 n) (r • y) = r • _
      rw [LinearMap.map_smulₛₗ, show (envelopeReindex s f (𝟙 n)).1.toRingHom r = r from
        envelopeReindex_id s f n r]
      rfl
    · intro r y
      rfl
    · intro r
      exact (envelopeDifferentialsMap_d s f (𝟙 n) r).trans
        (congrArg (dividedPowerDifferential (A := (s.A : Type u))
          (tensorPowerEnvelope s f n.len).object.dividedPowers) (envelopeReindex_id s f n r))
  exact DFunLike.congr_fun h x

/-- The induced maps on divided power differentials compose. -/
public lemma envelopeDifferentialsMap_comp {n m k : SimplexCategory} (φ : n ⟶ m) (ψ : m ⟶ k)
    (x : envelopeDifferentials s f n.len) :
    envelopeDifferentialsMap s f (φ ≫ ψ) x =
      envelopeDifferentialsMap s f ψ (envelopeDifferentialsMap s f φ x) := by
  have h : (envelopeDifferentialsMap s f (φ ≫ ψ)).toAddMonoidHom =
      (envelopeDifferentialsMap s f ψ).toAddMonoidHom.comp
        (envelopeDifferentialsMap s f φ).toAddMonoidHom := by
    apply differentials_hom_ext _ _ (envelopeReindex s f (φ ≫ ψ)).1.toRingHom
    · exact (envelopeDifferentialsMap s f (φ ≫ ψ)).map_smulₛₗ
    · intro r y
      change envelopeDifferentialsMap s f ψ (envelopeDifferentialsMap s f φ (r • y)) = _
      rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
      exact congrArg (fun z => z • envelopeDifferentialsMap s f ψ
        (envelopeDifferentialsMap s f φ y)) (envelopeReindex_comp s f φ ψ r).symm
    · intro r
      change envelopeDifferentialsMap s f (φ ≫ ψ) _ =
        envelopeDifferentialsMap s f ψ (envelopeDifferentialsMap s f φ _)
      rw [envelopeDifferentialsMap_d, envelopeDifferentialsMap_d, envelopeDifferentialsMap_d,
        envelopeReindex_comp]
  exact DFunLike.congr_fun h x

variable (hf : Function.Surjective f)

/-- The structure map of `Ω_{D(*)}` along a map of finite ordinals: the `p`-adic completion of
the map induced on the divided power differentials of the envelopes, semilinear over the
corresponding structure map of `D(*)`. -/
public noncomputable def completedEnvelopeDifferentialsMap {n m : SimplexCategory} (φ : n ⟶ m) :
    completedTensorPowerDifferentials s f n.len →ₛₗ[adicCompletionRingMap
        (envelopeReindex s f φ).1.toRingHom (map_pAdicIdeal_le s.p _)]
      completedTensorPowerDifferentials s f m.len where
  toFun := adicCompletionMapₛₗ (envelopeDifferentialsMap s f φ) (map_pAdicIdeal_le s.p _)
  map_add' := map_add _
  map_smul' := adicCompletionMapₛₗ_smul _ _

/-- The universal derivation of `D(n)` takes the image of an element of the envelope to the image
of its universal divided power differential. -/
public lemma tensorPowerDerivation_of (n : ℕ) (x : (tensorPowerEnvelope s f n).object) :
    tensorPowerDerivation s f hf n (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (dividedPowerDifferential (A := (s.A : Type u))
        (tensorPowerEnvelope s f n).object.dividedPowers x) :=
  (completedTensorPowerDifferential s f hf n).2.2 x

/-- **The structure maps of `Ω_{D(*)}` are compatible with the universal derivations.**  Both
sides are additive maps between `p`-adic completions, hence adically continuous, and they agree
on the dense image of the envelope, where the statement is the compatibility of the induced map
on divided power differentials with the universal differential. -/
public lemma completedEnvelopeDifferentialsMap_derivation {n m : SimplexCategory} (φ : n ⟶ m)
    (x : pAdicCompletedTensorPowerEnvelope s f hf n.len) :
    completedEnvelopeDifferentialsMap s f φ (tensorPowerDerivation s f hf n.len x) =
      tensorPowerDerivation s f hf m.len
        ((cosimplicialEnvelopeRing s f hf).map φ x) := by
  let q := adicCompletionMapₛₗ (envelopeDifferentialsMap s f φ) (map_pAdicIdeal_le s.p
    (envelopeReindex s f φ).1.toRingHom)
  let r := adicCompletionRingMap (envelopeReindex s f φ).1.toRingHom
    (map_pAdicIdeal_le s.p (envelopeReindex s f φ).1.toRingHom)
  let l := q.toAddMonoidHom.comp
    (tensorPowerDerivation s f hf n.len).toDerivation.toLinearMap.toAddMonoidHom
  let r' := (tensorPowerDerivation s f hf m.len).toDerivation.toLinearMap.toAddMonoidHom.comp
    r.toAddMonoidHom
  have h : l = r' :=
    adicCompletion_addMonoidHom_ext (pAdicIdeal_adicContinuous s.p l)
      (pAdicIdeal_adicContinuous s.p r') (by
        intro y
        change adicCompletionMapₛₗ (envelopeDifferentialsMap s f φ) _
            (tensorPowerDerivation s f hf n.len (AdicCompletion.of _ _ y)) =
          tensorPowerDerivation s f hf m.len
            (adicCompletionRingMap (envelopeReindex s f φ).1.toRingHom _
              (AdicCompletion.of _ _ y))
        refine Eq.trans ?_ (congrArg (fun z => tensorPowerDerivation s f hf m.len z)
          (adicCompletionRingMap_of (envelopeReindex s f φ).1.toRingHom
            (map_pAdicIdeal_le s.p (envelopeReindex s f φ).1.toRingHom) y)).symm
        refine Eq.trans ?_ (tensorPowerDerivation_of s f hf m.len
          ((envelopeReindex s f φ).1 y)).symm
        refine Eq.trans (congrArg
          (fun z => adicCompletionMapₛₗ (envelopeDifferentialsMap s f φ)
            (map_pAdicIdeal_le s.p (envelopeReindex s f φ).1.toRingHom) z)
          (tensorPowerDerivation_of s f hf n.len y)) ?_
        refine Eq.trans (adicCompletionMapₛₗ_of (envelopeDifferentialsMap s f φ)
          (map_pAdicIdeal_le s.p (envelopeReindex s f φ).1.toRingHom) _) ?_
        exact congrArg (AdicCompletion.of _ _) (envelopeDifferentialsMap_d s f φ y))
  exact DFunLike.congr_fun h x

/-- The degrees `Ω_{D(n)}` with the completed reindexing maps, as semilinear data over
`D(*)`. -/
public noncomputable def cosimplicialEnvelopeDifferentialsData :
    SemilinearCosimplicialModule.{max u w, max u w} (cosimplicialEnvelopeRing s f hf) where
  obj n := completedTensorPowerDifferentials s f n.len
  addCommGroup _n := inferInstance
  module n := inferInstanceAs (Module (pAdicCompletedTensorPowerEnvelope s f hf n.len)
    (completedTensorPowerDifferentials s f n.len))
  map φ := completedEnvelopeDifferentialsMap s f φ
  map_id_apply n x := adicCompletionMapₛₗ_id_apply _ _ (envelopeDifferentialsMap_id s f n) x
  map_comp_apply φ ψ x :=
    adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _ (envelopeDifferentialsMap_comp s f φ ψ) x

/-- **The cosimplicial module `Ω_{D(0)} → Ω_{D(1)} → Ω_{D(2)} → ⋯`** of `p`-adically completed
divided power differentials over the cosimplicial ring `D(*)`. -/
public noncomputable def cosimplicialEnvelopeDifferentials :
    CosimplicialModule (cosimplicialEnvelopeRing s f hf) :=
  (cosimplicialEnvelopeDifferentialsData s f hf).toCosimplicialModule

end CosimplicialDifferentials

/-! ### The cosimplicial envelope -/

section Envelope

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The cosimplicial envelope of a polynomial presentation.**  For an affine crystalline
situation and a surjection `P = A[x_i] → C`, the cosimplicial ring `D(*)` of `p`-adically
completed divided power envelopes of the kernels `J(n)` of the surjections
`P ⊗_A ⋯ ⊗_A P → C`, together with the cosimplicial module `Ω_{D(*)}` of `p`-adically completed
divided power differentials over it: a term of `Crystalline.CosimplicialEnvelope`, so the
statements of Tags 07L9 and 07LA apply to it.

No hypothesis is carried beyond the data `s`, `f` and the surjectivity `hf` which the type
itself mentions. -/
public noncomputable def cosimplicialEnvelope : CosimplicialEnvelope s f hf where
  ring := cosimplicialEnvelopeRing s f hf
  ringEquiv _n := RingEquiv.refl _
  ringEquiv_naturality φ q := cosimplicialEnvelopeRing_map_polynomial s f hf φ q
  ringEquiv_dp_naturality φ := cosimplicialEnvelopeRing_isDPMorphism s f hf φ
  differentials := cosimplicialEnvelopeDifferentials s f hf
  differentialsEquiv _n := AddEquiv.refl _
  differentialsEquiv_smul _n _r _x := rfl
  differentialsEquiv_naturality φ x :=
    completedEnvelopeDifferentialsMap_derivation s f hf φ x
  differentialsEquiv_adicContinuous φ :=
    adicCompletionMapₛₗ_continuous (envelopeDifferentialsMap s f φ) (map_pAdicIdeal_le s.p _)

/-- **Tag 07L9 for the constructed envelope.**  The identity endomorphism of the cosimplicial
module `Ω_{D(*)}` attached to the polynomial presentation `f` is homotopic to its zero
endomorphism: `Crystalline.id_cosimplicialEnvelopeDifferentials_homotopic_zero`, where that tag
sits, read on `Crystalline.cosimplicialEnvelope`. -/
public theorem cosimplicialEnvelope_differentials_homotopic_zero :
    Homotopic (𝟙 (cosimplicialEnvelopeDifferentials s f hf)) 0 :=
  id_cosimplicialEnvelopeDifferentials_homotopic_zero (cosimplicialEnvelope s f hf)

/-- **Tag 07LA for the constructed envelope.**  For every cosimplicial module `M_*` over the
cosimplicial ring `D(*)` of the polynomial presentation `f` and every `i > 0`, the cosimplicial
module `M_* ⊗̂_{D(*)} Ω^i_{D(*)}` is homotopic to zero:
`Crystalline.id_completedTensorCompletedForms_homotopic_zero`, where that tag sits, read on
`Crystalline.cosimplicialEnvelope`. -/
public theorem cosimplicialEnvelope_completedForms_homotopic_zero
    (M : CosimplicialModule (cosimplicialEnvelopeRing s f hf)) {i : ℕ} (hi : 0 < i) :
    Homotopic (𝟙 ((pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).completion
      (M ⊗ (pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).completion
        ((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) i).functor.obj
          (cosimplicialEnvelopeDifferentials s f hf))))) 0 :=
  id_completedTensorCompletedForms_homotopic_zero (cosimplicialEnvelope s f hf) M hi

end Envelope

end Crystalline

end
