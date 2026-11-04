module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Cech.Substrate

/-!
# Cohomology with support in a closed subset: the affine description

Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` be a finite family of elements, and let `M` be
an `A`-module.  This file constructs the affine description of the map `c_{f₁,…,f_c}` of
Tag 0G7Q: a map

`M/(f₁,…,f_c)M ⟶ Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})`

sending the class of `s ∈ M` to the class of the fraction `s/(f₁⋯f_c)`.

## Main definitions

* `Cech.topFraction`: the fraction `s/(f₁⋯f_c)`, as an element of the top term of the extended
  alternating Čech complex of `M`.
* `Cech.supportedFraction`: the map by which Tag 0G7R describes `c_{f₁,…,f_c}`.

## Main results

* `Cech.supportedFraction_mk`: the value of that map on the class of `s ∈ M` is the class of the
  fraction `s/(f₁⋯f_c)`.
* `Cech.smul_top_le_ker`: that value is well defined, i.e. the class of the fraction only depends
  on `s` modulo `(f₁,…,f_c)M`.
* `Cech.cechComplex_d_last`: the differential whose cokernel is taken is the last differential of
  the extended alternating Čech complex `Cech.cechComplex`.

## Implementation notes

Both explicit modules are read off the extended alternating Čech complex `Cech.cechComplex` of
Tag 0G7I.  Its degree-`c` term `Cech.cechTerm f M c` is a direct sum indexed by the `c`-element
subsets of `Fin c`, of which `Finset.univ` is the only one (`Cech.eq_topIndex`), so that term is
the single localization `M_{f₁⋯f_c}`; its degree-`(c-1)` term is `⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c}`; and the last
differential `Cech.cechD f M (c-1)` is the map whose cokernel appears in the statement.  That
cokernel is taken here as the quotient by the range of the differential, and the submodule
`(f₁,…,f_c)M` as `Ideal.span (Set.range f) • ⊤`.  The family is written `f : Fin (d + 1) → A`
because the empty family has no last differential.

The general map `c_{f₁,…,f_c} : i^*ℱ ⟶ ℋ^c_Z(ℱ)` of Tag 0G7Q *is* in this library, as
`Stacks.Perfect.FractionClass.fractionClass`, together with its cokernel-to-cokernel
presentation `Stacks.Perfect.SupportedFraction.supportedFractionClass`; the map built here is
nevertheless not obtained from it.  It is constructed directly between the two modules named in
Tag 0G7R, by dividing by the product of the equations and passing to the cokernel.  The step of
Tag 0G7Q that makes this well defined — the class of the fraction only depends on the numerator
modulo the equations — is `Cech.smul_top_le_ker` below, the affine counterpart of
`AlgebraicGeometry.ExtendedAlternatingCech.cokernel_π_app_eq_of_eq_mod_equations`.

*What Tag 0G7R asserts, and where it is proved.*  The example asserts that the map
`c_{f₁,…,f_c}` of Tag 0G7Q **can be described as** the map below, for `X = Spec A` and
`ℱ = M~`.  Both halves of the description are here — the map itself and the formula for its
value on the class of a section.  The identification with `c_{f₁,…,f_c}` is **proved**, in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AffineFractionClassBijective.lean`:
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_conj`.  The declaration it is
identified with is `Stacks.Perfect.SupportedFraction.supportedFractionClass`, which is
`c_{f₁,…,f_c}` in exactly the presentation the example uses,
`Coker((f₁,…,f_c) : ℱ^{⊕c} ⟶ ℱ) ⟶ Coker(lastDif f ℱ)`, with its value on the class of a section
given by `Stacks.Perfect.SupportedFraction.supportedFractionClass_mk`.  What the identification
needed was a pair of `A`-linear isomorphisms

`M/(f₁,…,f_c)M ≅ Γ(Spec A, Coker((f₁,…,f_c) : ℱ^{⊕c} ⟶ ℱ))` and
`Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c}) ≅ Γ(Spec A, Coker(lastDif g (M~)))`,

each normalised on the class of a section, over which `Γ(Spec A, -)` of
`supportedFractionClass` becomes `Cech.supportedFraction` below.

*Where the three pieces live.*  In
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AffineFractionClassComparison.lean`:
`Stacks.Perfect.AffineFractionClass.affineSourceComparison` is the source comparison and
`Stacks.Perfect.AffineFractionClass.bijective_affineSourceComparison` proves it is an
isomorphism, which is right exactness of `Γ(Spec A, -)` here, obtained from the exactness of
`M ↦ M~` and not from any vanishing theorem.  In
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AffineFractionClassTarget.lean`:
`Stacks.Perfect.AffineFractionClass.targetComparison` is the target comparison, normalised on
fractions, and `Stacks.Perfect.AffineFractionClass.supportedFraction_eq_targetComparison` is the
commuting square.  In `AffineFractionClassBijective.lean`:
`Stacks.Perfect.AffineFractionClass.bijective_targetComparison` shows the target comparison is
an isomorphism too, so the square is an identification of the two maps, and
`supportedFraction_eq_conj` states it.

The first file also carries the non-degeneracy certificate
`Stacks.Perfect.AffineFractionClass.supportedFraction_ne_zero`: for one equation which is a
nonzero non-unit of a domain the map below is not the zero map, so the description Tag 0G7R
asserts is not a description by zero;
`Stacks.Perfect.AffineFractionClass.Γ_supportedFractionClass_int_two_ne_zero` carries that
through the identification.

*The Čech half of the comparison also exists, independently.*
`Stacks.LocalCohomology.ordCochainEquivCechTerm`, together with
`Stacks.LocalCohomology.ordCochainToCechTerm_ordD` and
`Stacks.LocalCohomology.cechSign_ordIndex` in
`StacksFrontier/RingTheory/LocalCohomology/HigherDegree/OrderedCechComparison.lean`, matches the
ordered Čech complex of the standard covering of `Spec A` against `Cech.cechComplex`, Čech signs
included — its term comparison `Stacks.LocalCohomology.cechStandardTupleSectionsEquiv` is the
identification `Γ(D(f_{i₀} ⋯ f_{i_p}), M~) = M_{f_{i₀} ⋯ f_{i_p}}` — and the `sectionsIso` and
`differential_succ` fields of
`Stacks.Perfect.ExtendedAlternatingCech.ExtendedAlternatingCechData` present the sheaf-level
complex's sections as exactly that ordered Čech complex with `CechCochains.ordD`.  The route
actually taken in `AffineFractionClassBijective.lean` does not go through it: it compares only
the top degree and the degree below, where the two principal intersections are single basic
opens, so Mathlib's localization instance for `tilde` suffices.

*Passing from complexes to cokernels was the real step.*  It asks `Γ(Spec A, -)` to carry
`Coker(lastDif g (M~))` to the cokernel of the map it induces on sections, which is right
exactness of global sections on an affine scheme.  That is
`Stacks.Perfect.AffineFractionClass.surjective_Γ_cokernelπ` and `ker_Γ_cokernelπ`, proved from
quasi-coherence of the Čech terms — `Stacks.AlgebraicGeometry.AffinePushforward\
.pushforward_isQuasicoherent_of_isAffineHom`, Tag 02KG, applied to the inclusion of a
principal-open intersection — together with the exactness of `M ↦ M~`, so that a cokernel of
tildes is the tilde of a cokernel and global sections read it off.

## References

* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
-/

@[expose] public section

universe u v

namespace Cech

variable {R : Type u} [CommRing R] {d : ℕ} (f : Fin (d + 1) → R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-- The top degree of the extended alternating Čech complex of `f₁, …, f_c` is indexed by the
`c`-element subsets of `Fin c`, and the only one of those is the full set of indices. -/
theorem eq_topIndex (s : {s : Finset (Fin (d + 1)) // s.card = d + 1}) :
    s = ⟨Finset.univ, Finset.card_fin _⟩ :=
  Subtype.ext (Finset.eq_univ_of_card _ (by simpa using s.2))

/-- The differential `Cech.cechD f M d` is the last nonzero differential of the extended
alternating Čech complex, the one landing in the top degree `c = d + 1`. -/
theorem cechComplex_d_last :
    (cechComplex f M).d d (d + 1) = ModuleCat.ofHom (cechD f M d) := by
  simp [cechComplex]

/-- The fraction `m/(f₁⋯f_c)`, as an element of the top term `M_{f₁⋯f_c}` of the extended
alternating Čech complex of `M`. -/
noncomputable def topFraction : M →ₗ[R] cechTerm f M (d + 1) :=
  (DirectSum.lof R {s : Finset (Fin (d + 1)) // s.card = d + 1} (fun s => cechMod f M s.1)
      ⟨Finset.univ, Finset.card_fin _⟩).comp
    ((LocalizedModule.divBy
          (⟨∏ i, f i, Submonoid.mem_powers _⟩ : cechSub f Finset.univ)).comp
      (LocalizedModule.mkLinearMap (cechSub f Finset.univ) M))

/-- `Cech.topFraction` is the fraction with numerator `m` and denominator the product of all the
equations, placed in the unique summand of the top Čech term. -/
theorem topFraction_apply (m : M) :
    topFraction f M m =
      DirectSum.lof R {s : Finset (Fin (d + 1)) // s.card = d + 1} (fun s => cechMod f M s.1)
        ⟨Finset.univ, Finset.card_fin _⟩
        (LocalizedModule.mk m ⟨∏ i, f i, Submonoid.mem_powers _⟩) := by
  have hdiv : (LocalizedModule.divBy
        (⟨∏ i, f i, Submonoid.mem_powers _⟩ : cechSub f Finset.univ))
      (LocalizedModule.mkLinearMap (cechSub f Finset.univ) M m) =
      LocalizedModule.mk m ⟨∏ i, f i, Submonoid.mem_powers _⟩ := by
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.divBy_apply,
      LocalizedModule.liftOn_mk, one_mul]
  rw [topFraction, LinearMap.comp_apply, LinearMap.comp_apply, hdiv]

/-- Dividing by the product of all equations except `f i` in the `i`-th face of the Čech complex
and mapping to the top term gives the fraction with numerator `f i • m` over the full product. -/
theorem cechι_erase_mk (i : Fin (d + 1)) (m : M)
    (h : (Finset.univ : Finset (Fin (d + 1))).erase i ⊆ Finset.univ) :
    cechι f M h
        (LocalizedModule.mk m
          ⟨∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j, Submonoid.mem_powers _⟩) =
      LocalizedModule.mk (f i • m) ⟨∏ j, f j, Submonoid.mem_powers _⟩ := by
  classical
  have hprod : (∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j) * f i = ∏ j, f j :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have hmem : (∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j) ∈
      Submonoid.closure (f '' ((Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1)))) :=
    Submonoid.prod_mem _ fun j _ =>
      Submonoid.subset_closure ⟨j, Finset.mem_coe.2 (Finset.mem_univ j), rfl⟩
  refine IsLocalizedModule.smul_injective
    (LocalizedModule.mkLinearMap (cechSub f (Finset.univ : Finset (Fin (d + 1)))) M)
    (⟨_, hmem⟩ : Submonoid.closure
      (f '' ((Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))))) ?_
  simp only [Submonoid.smul_def]
  rw [← map_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk]
  rw [show (∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j) • f i • m =
      (⟨∏ j, f j, Submonoid.mem_powers _⟩ : cechSub f (Finset.univ : Finset (Fin (d + 1)))) • m by
    rw [Submonoid.smul_def, smul_smul, hprod]]
  rw [show (∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j) • m =
      (⟨∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j, Submonoid.mem_powers _⟩ :
        cechSub f ((Finset.univ : Finset (Fin (d + 1))).erase i)) • m from rfl]
  rw [LocalizedModule.mk_cancel, LocalizedModule.mk_cancel,
    ← LocalizedModule.mkLinearMap_apply, cechι_mk, LocalizedModule.mkLinearMap_apply]

/-- The `i`-th summand of the last Čech differential carries the fraction `m/(f₁⋯f̂ᵢ⋯f_c)` to the
fraction `f i • m/(f₁⋯f_c)` in the top term. -/
theorem lof_cechι_erase (i : Fin (d + 1)) (m : M)
    (hcard : (insert i ((Finset.univ : Finset (Fin (d + 1))).erase i)).card = d + 1)
    (hsub : (Finset.univ : Finset (Fin (d + 1))).erase i ⊆
      insert i ((Finset.univ : Finset (Fin (d + 1))).erase i)) :
    DirectSum.lof R {s : Finset (Fin (d + 1)) // s.card = d + 1} (fun s => cechMod f M s.1)
        ⟨insert i ((Finset.univ : Finset (Fin (d + 1))).erase i), hcard⟩
        (cechι f M hsub
          (LocalizedModule.mk m
            ⟨∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j,
              Submonoid.mem_powers _⟩)) =
      topFraction f M (f i • m) := by
  classical
  revert hcard hsub
  rw [Finset.insert_erase (Finset.mem_univ i)]
  intro hcard hsub
  rw [cechι_erase_mk f M i m hsub, topFraction_apply]

/-- The fraction `f i • m/(f₁⋯f_c)` is a boundary for the last Čech differential: it is the image
of `m/(f₁⋯f̂ᵢ⋯f_c)` in the `i`-th face, up to the Čech sign. -/
theorem topFraction_smul_mem_range (i : Fin (d + 1)) (m : M) :
    topFraction f M (f i • m) ∈ LinearMap.range (cechD f M d) := by
  classical
  have hcompl : ((Finset.univ : Finset (Fin (d + 1))).erase i)ᶜ = {i} := by
    simp [Finset.compl_erase]
  have hiT : i ∈ ((Finset.univ : Finset (Fin (d + 1))).erase i)ᶜ := by rw [hcompl]; simp
  have hcard : ((Finset.univ : Finset (Fin (d + 1))).erase i).card = d := by simp
  have hsq : cechSign ((Finset.univ : Finset (Fin (d + 1))).erase i) i *
      cechSign ((Finset.univ : Finset (Fin (d + 1))).erase i) i = 1 := by
    rw [cechSign, ← pow_add]
    exact Even.neg_one_pow ⟨_, rfl⟩
  refine ⟨cechSign ((Finset.univ : Finset (Fin (d + 1))).erase i) i •
    DirectSum.lof R {s : Finset (Fin (d + 1)) // s.card = d} (fun s => cechMod f M s.1)
      ⟨(Finset.univ : Finset (Fin (d + 1))).erase i, hcard⟩
      (LocalizedModule.mk m
        ⟨∏ j ∈ (Finset.univ : Finset (Fin (d + 1))).erase i, f j, Submonoid.mem_powers _⟩), ?_⟩
  rw [map_zsmul, cechD_lof, Finset.sum_eq_single_of_mem ⟨i, hiT⟩ (Finset.mem_attach _ _),
    smul_smul, hsq, one_zsmul]
  · exact lof_cechι_erase f M i m _ _
  · intro b _ hb
    refine absurd (Subtype.ext ?_) hb
    simpa using Finset.mem_compl.mp b.2

/-- The class of the fraction `m/(f₁⋯f_c)` in the cokernel of the last Čech differential depends
only on `m` modulo `(f₁,…,f_c)M`.  This is the affine form of step 4 of Tag 0G7Q. -/
theorem smul_top_le_ker :
    Ideal.span (Set.range f) • (⊤ : Submodule R M) ≤
      LinearMap.ker ((LinearMap.range (cechD f M d)).mkQ.comp (topFraction f M)) := by
  classical
  have key : ∀ r ∈ Ideal.span (Set.range f), ∀ m : M,
      (LinearMap.range (cechD f M d)).mkQ.comp (topFraction f M) (r • m) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro m
        exact (Submodule.Quotient.mk_eq_zero _).2 (topFraction_smul_mem_range f M i m)
    | zero => intro m; simp
    | add x y _ _ hx hy => intro m; rw [add_smul, map_add, hx, hy, add_zero]
    | smul a x _ hx => intro m; rw [smul_eq_mul, mul_smul, map_smul, hx, smul_zero]
  rw [Submodule.smul_le]
  intro r hr m _
  exact key r hr m

/-- **Cohomology with support in a closed subset, affine description.**  For a family of
equations `f₁, …, f_c ∈ A` and an `A`-module `M`, the map
`M/(f₁,…,f_c)M ⟶ Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})` that divides by the product of the
equations: it sends the class of `s ∈ M` to the class of `s/(f₁⋯f_c)`.

This is the map by which Tag 0G7R describes `c_{f₁,…,f_c}` of Tag 0G7Q when `X = Spec A` and
`ℱ = M~`.  That the two agree is proved in `AffineFractionClassBijective.lean`; see the
implementation notes. -/
noncomputable def supportedFraction :
    (M ⧸ Ideal.span (Set.range f) • (⊤ : Submodule R M)) →ₗ[R]
      cechTerm f M (d + 1) ⧸ LinearMap.range (cechD f M d) :=
  Submodule.liftQ _ ((LinearMap.range (cechD f M d)).mkQ.comp (topFraction f M))
    (smul_top_le_ker f M)

/-- The affine description of `c_{f₁,…,f_c}` sends the class of a section `s ∈ M` to the class of
the fraction `s/(f₁⋯f_c)` in the cokernel of the last Čech differential. -/
theorem supportedFraction_mk (s : M) :
    supportedFraction f M (Submodule.Quotient.mk s) =
      Submodule.Quotient.mk
        (DirectSum.lof R {t : Finset (Fin (d + 1)) // t.card = d + 1}
          (fun t => cechMod f M t.1) ⟨Finset.univ, Finset.card_fin _⟩
          (LocalizedModule.mk s ⟨∏ i, f i, Submonoid.mem_powers _⟩)) := by
  rw [← topFraction_apply]
  rfl

end Cech

end
