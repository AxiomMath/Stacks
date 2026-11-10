module

public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.RingTheory.Etale.IdempotentDetectingResidue

/-!
# A clopen part of a fibre of a proper morphism extends over an étale neighbourhood

Let `ψ : X ⟶ T` be a proper morphism of schemes, `v ∈ T` and `C` an open and closed subset of the
fibre `X_v`.  This file proves that, after an étale base change `τ : Spec R' ⟶ T` hitting `v` at
a point `v'`, there is an open and closed subset `A` of `X ×_T Spec R'` whose trace on the fibre
over `v'` is the preimage of `C`.

This is false without the étale base change — for `Spec ℤ[i] ⟶ Spec ℤ` the fibre over `5` has
two points but `Spec ℤ[i]` is connected — and it is the scheme-theoretic input of the
connectedness clause of the Stein factorization of a proper morphism of algebraic spaces
(Stacks 0A1C) in this library.

## Main results

* `AlgebraicGeometry.exists_etale_isClopen_extension_of_isProper`.

## Implementation notes

`C` is the nonvanishing locus of an idempotent `ē` of `Γ(X_v, 𝒪)`.  By Stacks 0G7X
(`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`) `ē` is the restriction
of a section `a₀` of `𝒪_X` over `ψ⁻¹(U)` for an open neighbourhood `U` of `v`; choose an affine
open `W ∋ v` inside `U`, with ring `R = Γ(T, W)`, and let `a` be the restriction of `a₀` to
`Y = X ×_T Spec R`.  As `Y ⟶ Spec R` is universally closed, `a` is integral over `R`, so
`Algebra.exists_etale_isIdempotentElem_detecting_sub_one` gives an étale `R → R'`, a prime `p'`
over the prime of `v`, and an idempotent `ε` of `R' ⊗_R Γ(Y, 𝒪)` which, at the points over `p'`,
is nonzero exactly where `a ≡ 1`, that is exactly over `C`.  Its image in
`Γ(X ×_T Spec R', 𝒪)` cuts out `A`.

## References

* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 00UK](https://stacks.math.columbia.edu/tag/00UK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- For an idempotent `e`, the nonvanishing locus of `e - 1` is the complement of that of `e`. -/
theorem Scheme.mem_basicOpen_sub_one_of_isIdempotentElem (Y : Scheme.{u}) (e : Γ(Y, ⊤))
    (he : IsIdempotentElem e) (x : Y) :
    x ∈ Y.basicOpen (e - 1) ↔ x ∉ Y.basicOpen e := by
  rw [← Scheme.mem_basicOpen_one_sub_of_isIdempotentElem Y e he x, Scheme.mem_basicOpen_top,
    Scheme.mem_basicOpen_top, ← neg_sub, map_neg, IsUnit.neg_iff]

/-- The nonvanishing locus of an idempotent global section is closed. -/
private theorem Scheme.isClosed_basicOpen_of_isIdempotentElem (Y : Scheme.{u}) (e : Γ(Y, ⊤))
    (he : IsIdempotentElem e) : IsClosed (Y.basicOpen e : Set Y) := by
  have hc : ((Y.basicOpen e : Set Y))ᶜ = Y.basicOpen (1 - e) := by
    ext x
    exact (Scheme.mem_basicOpen_one_sub_of_isIdempotentElem Y e he x).symm
  exact isOpen_compl_iff.mp (hc ▸ (Y.basicOpen (1 - e)).isOpen)

/-- If `g` lands in `U`, the first projection of `X ×_T Z` lands in the preimage of `U`. -/
private theorem Scheme.top_le_pullback_fst_preimage_preimage {X Z T : Scheme.{u}} (f : X ⟶ T)
    (g : Z ⟶ T) {U : T.Opens} (h : Set.range g ⊆ U) :
    (⊤ : (pullback f g).Opens) ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
  intro y _
  change f (pullback.fst f g y) ∈ U
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact h (Set.mem_range_self _)

/-- A prime of an algebra over `Γ(T, W)` lying over the prime of `v ∈ W` maps to `v`. -/
private theorem IsAffineOpen.fromSpec_map_algebraMap_of_liesOver {T : Scheme.{u}} {W : T.Opens}
    (hW : IsAffineOpen W) {v : T} (hvW : v ∈ W) {R' : Type u} [CommRing R']
    [Algebra Γ(T, W) R'] (x : Spec (CommRingCat.of R'))
    (h : x.asIdeal.LiesOver (hW.primeIdealOf ⟨v, hvW⟩).asIdeal) :
    hW.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) R')) x) = v := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(T, W) R')) x =
      hW.primeIdealOf ⟨v, hvW⟩ := by
    rw [Spec.map_apply]
    exact PrimeSpectrum.ext (Ideal.over_def x.asIdeal _).symm
  rw [h1]
  exact hW.fromSpec_primeIdealOf ⟨v, hvW⟩

/-- A section `a₀` restricting to an idempotent `ē` on the fibre: a point of the fibre lies in
the nonvanishing locus of `a₀ - 1` exactly when it is outside the nonvanishing locus `C` of `ē`. -/
private theorem Scheme.Hom.fiberι_mem_basicOpen_sub_one_iff {X T : Scheme.{u}} (ψ : X ⟶ T) {v : T}
    {U : T.Opens} (hvU : v ∈ U) {a₀ : Γ(X, ψ ⁻¹ᵁ U)} {ē : Γ(ψ.fiber v, ⊤)}
    (hē : IsIdempotentElem ē)
    (ha₀ : (ψ.fiberι v).appLE (ψ ⁻¹ᵁ U) ⊤
      (Stacks.AlgebraicGeometry.Fibres.fiberι_preimage_preimage_eq_top ψ hvU).ge a₀ = ē)
    {C : (ψ.fiber v).Opens} (hēC : (ψ.fiber v).basicOpen ē = C) (c : ψ.fiber v) :
    ψ.fiberι v c ∈ X.basicOpen (a₀ - 1) ↔ c ∉ C := by
  have hē1 : ((ψ.fiberι v).appLE (ψ ⁻¹ᵁ U) ⊤
      (Stacks.AlgebraicGeometry.Fibres.fiberι_preimage_preimage_eq_top ψ hvU).ge).hom (a₀ - 1) =
        ē - 1 := by
    rw [map_sub, map_one, ha₀]
  have hmem := congrArg (fun O : (ψ.fiber v).Opens => c ∈ O)
    (Scheme.basicOpen_appLE (ψ.fiberι v) ⊤ (ψ ⁻¹ᵁ U)
      (Stacks.AlgebraicGeometry.Fibres.fiberι_preimage_preimage_eq_top ψ hvU).ge (a₀ - 1))
  simp only [hē1] at hmem
  rw [Scheme.mem_basicOpen_sub_one_of_isIdempotentElem _ ē hē, hēC] at hmem
  exact ((Iff.of_eq hmem).trans ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩).symm

/-- **A clopen part of a fibre of a proper morphism extends, after an étale base change, to a
clopen subset.**  Let `ψ : X ⟶ T` be proper, `v ∈ T` and `C` an open subset of the fibre `X_v`
which is also closed.  There are a ring `R'`, an étale morphism `τ : Spec R' ⟶ T`, a point `v'`
of `Spec R'` over `v`, and an open subset `A` of `X ×_T Spec R'` which is also closed, such that a
point `z` of `X ×_T Spec R'` over `v'` lies in `A` exactly when its image in `X`, a point of the
fibre over `v`, lies in `C`. -/
theorem exists_etale_isClopen_extension_of_isProper {X T : Scheme.{u}} (ψ : X ⟶ T)
    [IsProper ψ] (v : T) (C : (ψ.fiber v).Opens) (hC : IsClosed (C : Set (ψ.fiber v))) :
    ∃ (R' : CommRingCat.{u}) (τ : Spec R' ⟶ T) (_ : Etale τ) (v' : Spec R'), τ v' = v ∧
      ∃ A : (pullback ψ τ).Opens, IsClosed (A : Set ↥(pullback ψ τ)) ∧
        ∀ z : ↥(pullback ψ τ), pullback.snd ψ τ z = v' →
          (z ∈ A ↔ ∃ c ∈ C, ψ.fiberι v c = pullback.fst ψ τ z) := by
  classical
  obtain ⟨ē, hē, hēC⟩ := exists_isIdempotentElem_basicOpen_eq (ψ.fiber v) C hC
  obtain ⟨U, hvU, a₀, ha₀⟩ :=
    Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper ψ v ē hē
  obtain ⟨W, hW, hvW, hWU⟩ := exists_isAffineOpen_mem_and_subset hvU
  set R : CommRingCat.{u} := Γ(T, W)
  set Y := pullback ψ hW.fromSpec
  set π : Y ⟶ Spec R := pullback.snd ψ hW.fromSpec
  have hfstY : (⊤ : Y.Opens) ≤ pullback.fst ψ hW.fromSpec ⁻¹ᵁ ψ ⁻¹ᵁ U :=
    Scheme.top_le_pullback_fst_preimage_preimage ψ hW.fromSpec
      fun _ hx => hWU (by rwa [hW.range_fromSpec] at hx)
  let a : Γ(Y, ⊤) := ((pullback.fst ψ hW.fromSpec).appLE (ψ ⁻¹ᵁ U) ⊤ hfstY).hom a₀
  let : Algebra R Γ(Y, ⊤) := (π.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom).toAlgebra
  have hint : (algebraMap R Γ(Y, ⊤)).IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed π)
  set p : PrimeSpectrum R := hW.primeIdealOf ⟨v, hvW⟩
  obtain ⟨R', _, _, _, p', _, hp'p, ε, hε, hdet⟩ :=
    Algebra.exists_etale_isIdempotentElem_detecting_sub_one (hint a) p.asIdeal
  let φ : R ⟶ CommRingCat.of R' := CommRingCat.ofHom (algebraMap R R')
  have hφ : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let τ : Spec (CommRingCat.of R') ⟶ T := Spec.map φ ≫ hW.fromSpec
  let v' : Spec (CommRingCat.of R') := ⟨p', inferInstance⟩
  have hτv : τ v' = v := hW.fromSpec_map_algebraMap_of_liesOver hvW v' hp'p
  refine ⟨CommRingCat.of R', τ, inferInstance, v', hτv, ?_⟩
  let P := pullback ψ τ
  let μ : P ⟶ Y := pullback.lift (pullback.fst ψ τ) (pullback.snd ψ τ ≫ Spec.map φ)
    (by rw [pullback.condition, Category.assoc])
  have hμπ : μ ≫ π = pullback.snd ψ τ ≫ Spec.map φ := pullback.lift_snd _ _ _
  have hμfst : μ ≫ pullback.fst ψ hW.fromSpec = pullback.fst ψ τ := pullback.lift_fst _ _ _
  let : Algebra R Γ(P, ⊤) := (μ.appTop.hom.comp (algebraMap R Γ(Y, ⊤))).toAlgebra
  let g : Γ(Y, ⊤) →ₐ[R] Γ(P, ⊤) := { μ.appTop.hom with commutes' := fun _ => rfl }
  have hkey : φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ (pullback.snd ψ τ).appTop =
      (Scheme.ΓSpecIso R).inv ≫ π.appTop ≫ μ.appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, ← hμπ, Scheme.Hom.comp_appTop]
  have hcompat : ∀ r : R, (pullback.snd ψ τ).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (algebraMap R R' r)) =
        algebraMap R Γ(P, ⊤) r := fun r => congrArg (fun k => k.hom r) hkey
  let f : R' →ₐ[R] Γ(P, ⊤) :=
    { (pullback.snd ψ τ).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom with
      commutes' := hcompat }
  let Θ : R' ⊗[R] Γ(Y, ⊤) →+* Γ(P, ⊤) := (Algebra.TensorProduct.productMap f g).toRingHom
  have hΘ : ∀ (s : R') (t : Γ(Y, ⊤)), Θ (s ⊗ₜ t) = f s * g t := fun s t =>
    Algebra.TensorProduct.productMap_apply_tmul f g s t
  refine ⟨P.basicOpen (Θ ε), ?_, ?_⟩
  · exact P.isClosed_basicOpen_of_isIdempotentElem _ (hε.map Θ)
  · intro z hz
    let χ : R' ⊗[R] Γ(Y, ⊤) →+* P.residueField z := (P.evaluation ⊤ z trivial).hom.comp Θ
    have hχeval : ∀ t, χ t ≠ 0 ↔ z ∈ P.basicOpen (Θ t) := fun t =>
      P.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) z trivial (Θ t)
    have hker : RingHom.ker (χ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R))) = p' := by
      ext s
      rw [RingHom.mem_ker, ← not_iff_not, ← ne_eq]
      change χ (s ⊗ₜ 1) ≠ 0 ↔ s ∉ p'
      rw [hχeval, hΘ, map_one, mul_one]
      change z ∈ P.basicOpen ((pullback.snd ψ τ).app ⊤ |>.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom s)) ↔ _
      rw [← Scheme.Hom.preimage_basicOpen, Scheme.Hom.mem_preimage, hz, basicOpen_eq_of_affine]
      exact PrimeSpectrum.mem_basicOpen s v'
    change z ∈ P.basicOpen (Θ ε) ↔ _
    rw [← hχeval, hdet χ hker, ← not_iff_not, ← ne_eq, hχeval, hΘ, map_one, one_mul]
    change z ∈ P.basicOpen ((μ.app ⊤).hom (a - 1)) ↔ _
    have hfz : ψ (pullback.fst ψ τ z) = v := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz, hτv]
    obtain ⟨c, hc⟩ : pullback.fst ψ τ z ∈ Set.range (ψ.fiberι v) := by
      rwa [Scheme.Hom.range_fiberι]
    have hrhs : (∃ c' ∈ C, ψ.fiberι v c' = pullback.fst ψ τ z) ↔ c ∈ C :=
      ⟨fun ⟨c', hc'C, hc'⟩ => ((ψ.fiberι v).isEmbedding.injective (hc'.trans hc.symm)) ▸ hc'C,
        fun h => ⟨c, h, hc⟩⟩
    rw [hrhs, ← Scheme.Hom.preimage_basicOpen, Scheme.Hom.mem_preimage]
    have ha1 : a - 1 = ((pullback.fst ψ hW.fromSpec).appLE (ψ ⁻¹ᵁ U) ⊤ hfstY).hom (a₀ - 1) := by
      simp [a]
    rw [ha1, Scheme.basicOpen_appLE]
    have hiff : μ z ∈ (⊤ ⊓ pullback.fst ψ hW.fromSpec ⁻¹ᵁ X.basicOpen (a₀ - 1) : Y.Opens) ↔
        pullback.fst ψ hW.fromSpec (μ z) ∈ X.basicOpen (a₀ - 1) :=
      ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
    rw [hiff, ← Scheme.Hom.comp_apply, hμfst, ← hc]
    exact ψ.fiberι_mem_basicOpen_sub_one_iff hvU hē ha₀ hēC c

end AlgebraicGeometry

end
