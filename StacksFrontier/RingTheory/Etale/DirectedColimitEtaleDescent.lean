module

public import StacksFrontier.RingTheory.Etale.StandardPresentationJacobian

/-!
# An étale algebra over a directed colimit of rings comes from a stage

Let `A = colim_i A_i` be a directed colimit of commutative rings and let `A → D` be étale with
`Spec(D) → Spec(A)` surjective.  Then there is a stage `i`, as late as one likes, and a standard
presentation `C_i = A_i[x_1, …, x_n]/(q_1, …, q_n)` over that stage, such that `A_i → C_i` is
étale, `Spec(C_i) → Spec(A_i)` is surjective, and `D = A ⊗_{A_i} C_i`.

This is **the commutative-algebra core of Stacks 07SQ**, the lemma that an inverse system of
quasi-compact quasi-separated algebraic spaces with affine transition morphisms and affine limit
has an affine stage.  In the source's proof `A = Γ(X, 𝒪_X)`, `A_i = Γ(X_i, 𝒪_{X_i})`,
`D = Γ(U, 𝒪_U)` for an affine étale surjective chart `U ⟶ X`, and `C_i = Γ(U_i, 𝒪_{U_i})`; the
stage found here is the one at which the source forms its cartesian square (Stacks 084U) and
concludes by fpqc descent of affineness.

The colimit is taken elementwise, exactly as in
`StacksFrontier/RingTheory/MvPolynomial/DirectedColimit.lean` and
`StacksFrontier/RingTheory/Etale/DirectedColimitPresentation.lean`: the system is `G : ι → Type v`
with transition maps `f`, the vertex is `A` with maps `φ i : G i →+* A`, and the three hypotheses
`hφ`, `hsurj`, `hzero` say that the `φ i` are compatible with the transitions, that every element
of `A` comes from a stage, and that an element of a stage dying in `A` already dies at a later
stage.  Over a directed index set those three are exactly `A = colim_i G i`.  They are supplied
geometrically by `AlgebraicGeometry.exists_appTop_eq_of_isAffine_of_isLimit_of_directed` and
`AlgebraicGeometry.exists_ge_appTop_map_eq_zero_of_isAffine_of_isLimit_of_directed`, and
algebraically by `Ring.DirectLimit.exists_of` and `Ring.DirectLimit.of.zero_exact`.

## Main results

* `MvPolynomial.exists_ge_surjective_comap_quotient_of_algEquiv`: Stacks 07RR for a presented
  algebra, with the identification of the presented algebra with the given one supplied as an
  algebra equivalence rather than as a pair of raw ring maps.
* `Algebra.Etale.exists_ge_etale_surjective_tensor_quotient_of_directed`: **the statement above**,
  the commutative-algebra core of Stacks 07SQ.

## Implementation notes

*Why three stages and not one.*  The three conclusions become true at three different indices and
each has to be carried up to the next.  Lifting the polynomials `g_λ` of the presentation of `D`
over `A` to a stage is `MvPolynomial.exists_ge_forall_map_eq_of_directed` and reaches `j₁`;
invertibility of the Jacobian determinant of the lifted family is
`MvPolynomial.exists_ge_isUnit_detJacobian_of_directed` and reaches `j₂ ≥ j₁`; surjectivity of
the spectrum map is `MvPolynomial.exists_ge_surjective_comap_quotient_of_directed` and reaches
`j₃ ≥ j₂`.  Of the two properties already in hand at `j₂`, invertibility of the Jacobian is the
one that survives the last step, by `MvPolynomial.isUnit_detJacobian_map`; étaleness is therefore
read off at `j₃` from the Jacobian by `Algebra.etale_mvPolynomialQuotient_of_isUnit_det` rather
than transported, which is why the Jacobian — and not merely étaleness — is what
`Algebra.Etale.exists_isUnit_detJacobian_algEquiv_quotient_span_range` has to extract from
Stacks 00U9.

*The algebra structure on `A` over a stage.*  `A` is an algebra over `G j` through `φ j`, which is
not an instance; the statement therefore opens with `letI := (φ j).toAlgebra` inside the
existential, as `MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_directed` does.  For the same
reason the base change is stated as `Nonempty (… ≃ₐ[A] D)` rather than as an equality of rings.

*Surjectivity is of the spectrum map, not of the ring map.*  `Spec(D) → Spec(A)` surjective is
`Function.Surjective (PrimeSpectrum.comap (algebraMap A D))`, which is the form the source's
reference to Stacks 07RR uses and the form
`StacksFrontier/RingTheory/Spectrum/Prime/DirectedColimit.lean` proves.

### Not proved here

**Stacks 07SQ itself is not proved here and no `@[stacks]` attribute appears in this file.**  What
is proved is the commutative-algebra half of the source's argument; the geometric half needs, in
Situation 084R (`AlgebraicGeometry.Space.LimitSituation`), two further things.

*The colimit of the rings of global functions.*  The elementwise colimit hypotheses `hφ`, `hsurj`
and `hzero` above have to be supplied for `A = Γ(X, 𝒪_X)` and `G i = Γ(X_i, 𝒪_{X_i})`, which is
Stacks 07SI, the predicate `AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean`.  **Nothing in this
development produces that predicate without hypotheses.**  For the structure sheaf the frontier is
`AlgebraicGeometry.Space.LimitSituation.isSectionsColimit_of_naturality_of_unit` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/ChartLimitEqualizerPresentation.lean`, where both
equalizer presentations are supplied (`.chartEqualizerPresentation` and
`.chartLimitEqualizerPresentation`) and only its two naturality hypotheses `he` and `heT` remain:
the compatibility of the components of
`AlgebraicGeometry.Space.LimitSituation.stageModuleUnitIso` and of `.limitModuleUnitIso` with
`AlgebraicGeometry.Space.modulePullbackCompIso`.  Those two are the single remaining mathematical
input of Stacks 07SI, and so of Stacks 07SQ and of Stacks 07SR.

*The concluding descent.*  Given the stage this file produces, the source forms the cartesian
square of Stacks 084U and concludes that `X_j ⟶ Spec(G j)` is affine because affineness of a
morphism is fpqc local on the base.  Both of those are available:
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isIso_mapAt` carries Stacks 084S,
`AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc` carries Stacks 041Z with no hypothesis
left, and `AlgebraicGeometry.Space.IsAffineHom.isAffineSpace_source` turns affineness over the
affine `Spec(G j)` into affineness of the stage.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
-/

@[expose] public section

universe u v w

open MvPolynomial TensorProduct

namespace MvPolynomial

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **Stacks 07RR for a presented algebra, through an algebra equivalence.**  This is
`MvPolynomial.exists_ge_surjective_comap_quotient_of_directed` with its two ring maps `χ` and `θ`
and their compatibility replaced by the datum that actually occurs: an identification of the
given `A`-algebra `D` with the base change `A[x] ⧸ (φ_i q)` of the presented algebra
`G i[x] ⧸ (q)`.  The ring map `θ` is then the map of quotients induced by `map (φ i)`, read
through that identification, and the compatibility is `AlgEquiv.commutes`. -/
theorem exists_ge_surjective_comap_quotient_of_algEquiv [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {κ : Type*} [Finite κ] {i : ι} (q : κ → MvPolynomial κ (G i))
    {D : Type*} [CommRing D] [Algebra A D]
    (e : D ≃ₐ[A] MvPolynomial κ A ⧸ Ideal.span (Set.range fun k ↦ map (φ i) (q k)))
    (hD : Function.Surjective (PrimeSpectrum.comap (algebraMap A D))) :
    ∃ (j : ι) (h : i ≤ j), Function.Surjective (PrimeSpectrum.comap
      (algebraMap (G j) (MvPolynomial κ (G j) ⧸
        Ideal.span (Set.range fun k ↦ map (f i j h) (q k))))) := by
  have hle : Ideal.span (Set.range q) ≤
      (Ideal.span (Set.range fun k ↦ map (φ i) (q k))).comap (MvPolynomial.map (φ i)) := by
    rw [Ideal.span_le]
    rintro x ⟨k, rfl⟩
    exact Ideal.subset_span ⟨k, rfl⟩
  refine exists_ge_surjective_comap_quotient_of_directed hφ hsurj hzero q (algebraMap A D)
    (e.symm.toAlgHom.toRingHom.comp (Ideal.quotientMap
      (Ideal.span (Set.range fun k ↦ map (φ i) (q k))) (MvPolynomial.map (φ i)) hle)) ?_ hD
  refine RingHom.ext fun x ↦ ?_
  show algebraMap A D (φ i x) =
    e.symm (Ideal.quotientMap (Ideal.span (Set.range fun k ↦ map (φ i) (q k)))
      (MvPolynomial.map (φ i)) hle (Ideal.Quotient.mk (Ideal.span (Set.range q)) (C x)))
  rw [Ideal.quotientMap_mk, map_C]
  exact (e.symm.commutes (φ i x)).symm

end MvPolynomial

namespace Algebra.Etale

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **An étale algebra with surjective spectrum map over a directed colimit of rings comes from a
stage.**  Let `A = colim_i G i` be a directed colimit of commutative rings, taken elementwise
through `hφ`, `hsurj` and `hzero`, and let `D` be an étale `A`-algebra with `Spec(D) → Spec(A)`
surjective.  Then beyond any prescribed index there is a stage `j` and a family
`q : Fin n → G j[x_1, …, x_n]` of polynomials indexed by the variables such that
`C = G j[x] ⧸ (q)` is étale over `G j`, `Spec(C) → Spec(G j)` is surjective, and
`D = A ⊗_{G j} C`.

This is the commutative-algebra core of Stacks 07SQ: with `A` the ring of global functions of the
limit, `G j` that of the stage `X_j` and `D` that of an affine étale surjective chart of the
limit, it produces the stage at which the source's cartesian square of Stacks 084U is formed. -/
theorem exists_ge_etale_surjective_tensor_quotient_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    (D : Type w) [CommRing D] [Algebra A D] [Algebra.Etale A D]
    (hD : Function.Surjective (PrimeSpectrum.comap (algebraMap A D))) (i₀ : ι) :
    ∃ (j : ι) (_ : i₀ ≤ j) (n : ℕ) (q : Fin n → MvPolynomial (Fin n) (G j)),
      letI := (φ j).toAlgebra
      Algebra.Etale (G j) (MvPolynomial (Fin n) (G j) ⧸ Ideal.span (Set.range q)) ∧
        Function.Surjective (PrimeSpectrum.comap (algebraMap (G j)
          (MvPolynomial (Fin n) (G j) ⧸ Ideal.span (Set.range q)))) ∧
        Nonempty (A ⊗[G j] (MvPolynomial (Fin n) (G j) ⧸ Ideal.span (Set.range q)) ≃ₐ[A] D) := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨n, g, hgu, ⟨eD⟩⟩ :=
    Algebra.Etale.exists_isUnit_detJacobian_algEquiv_quotient_span_range A D
  obtain ⟨j₁, hj₁, q, hq⟩ := MvPolynomial.exists_ge_forall_map_eq_of_directed hφ hsurj g i₀
  have hq' : (fun k ↦ map (φ j₁) (q k)) = g := funext hq
  obtain ⟨j₂, hj₂, hu₂⟩ :=
    MvPolynomial.exists_ge_isUnit_detJacobian_of_directed hφ hsurj hzero q (hq' ▸ hgu)
  set q₂ : Fin n → MvPolynomial (Fin n) (G j₂) := fun k ↦ map (f j₁ j₂ hj₂) (q k) with hq₂def
  have hq₂ : (fun k ↦ map (φ j₂) (q₂ k)) = g := by
    funext k
    rw [hq₂def, MvPolynomial.map_map_eq_of_comp hφ, hq]
  obtain ⟨j₃, hj₃, hsurj₃⟩ := MvPolynomial.exists_ge_surjective_comap_quotient_of_algEquiv
    hφ hsurj hzero q₂ (hq₂ ▸ eD) hD
  refine ⟨j₃, hj₁.trans (hj₂.trans hj₃), n, fun k ↦ map (f j₂ j₃ hj₃) (q₂ k), ?_, hsurj₃, ?_⟩
  · exact Algebra.etale_mvPolynomialQuotient_of_isUnit_det _
      (MvPolynomial.isUnit_detJacobian_map (f j₂ j₃ hj₃) q₂ hu₂)
  · have hq₃ : (fun k ↦ map (φ j₃) (map (f j₂ j₃ hj₃) (q₂ k))) = g := by
      funext k
      rw [MvPolynomial.map_map_eq_of_comp hφ]
      exact congrFun hq₂ k
    obtain ⟨t⟩ := MvPolynomial.nonempty_quotientSpanEquiv_tensor_of_directed
      (φ := φ) (fun k ↦ map (f j₂ j₃ hj₃) (q₂ k))
    exact ⟨t.trans ((hq₃ ▸ eD).symm)⟩

end Algebra.Etale

end
