module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Etale.NonfiniteGenerators

/-!
# Dominating a finite étale cover of a closed subscheme of affine space

Let `k` be a field of characteristic `p > 0`, let `Z ⊆ 𝐀ⁿ_k` be a closed subscheme and let
`Y ⟶ Z` be finite étale. Then there is a finite étale morphism `f : U ⟶ 𝐀ⁿ_k` and an immersion
`Y ⟶ f⁻¹(Z)` over `Z` which is both open and closed.

In algebra: `Z = Spec A` with `A = k[x₁, …, xₙ] / I` and `Y = Spec B` with `A ⟶ B` finite étale.
Lifting an étale algebra across the surjection `k[x₁, …, xₙ] ⟶ A` gives an étale presentation of
`B`, and lowering its nonfinite-generator invariant to zero makes the étale map
`k[x₁, …, xₙ] ⟶ C` finite. The surjection `C ⟶ B` it comes with is a closed immersion on
spectra, and it is étale because `Y ⟶ Z` and `U ⟶ 𝐀ⁿ_k` both are, hence an open immersion as
well.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_openClosed_pullback` — the finite étale cover of affine
  space and the open-and-closed immersion over the closed subscheme.

## Implementation notes

Affine space is the spectrum of `MvPolynomial (Fin n) k`, and `f⁻¹(Z)` is the categorical
pullback of `f` along the closed immersion `i : Z ⟶ 𝐀ⁿ_k`; that the immersion is over `Z` is the
equation `j ≫ pullback.snd f i = g`. That `j` is open is
`AlgebraicGeometry.isOpenImmersion_of_etale_universallyInjective`, applied to the monomorphism
underlying the closed immersion.

## References

* [Stacks Project, Tag 0G1H](https://stacks.math.columbia.edu/tag/0G1H)
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace Stacks.Etale

/-- In positive characteristic, a finite étale algebra `B` over `k[x₁, …, xₙ] ⧸ I` is a quotient
of a finite étale `k[x₁, …, xₙ]`-algebra, compatibly with the quotient map. -/
private theorem exists_finite_etale_surjection_of_quotient
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k)) (B : Type u) [CommRing B]
    [Algebra (MvPolynomial (Fin n) k ⧸ I) B] [Algebra k B]
    [IsScalarTower k (MvPolynomial (Fin n) k ⧸ I) B]
    [Module.Finite (MvPolynomial (Fin n) k ⧸ I) B]
    [Algebra.Etale (MvPolynomial (Fin n) k ⧸ I) B] :
    ∃ (C : Type u) (_ : CommRing C) (ψ : MvPolynomial (Fin n) k →+* C) (τ₀ : C →+* B),
      ψ.Etale ∧ ψ.Finite ∧ Function.Surjective τ₀ ∧
        τ₀.comp ψ = (algebraMap (MvPolynomial (Fin n) k ⧸ I) B).comp (Ideal.Quotient.mk I) := by
  let P := MvPolynomial (Fin n) k
  let : Algebra P B := ((algebraMap (P ⧸ I) B).comp (Ideal.Quotient.mk I)).toAlgebra
  have : IsScalarTower P (P ⧸ I) B := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k P B := .of_algebraMap_eq fun x => by
    change _ = algebraMap (P ⧸ I) B (Ideal.Quotient.mk I (algebraMap k P x))
    rw [Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
  obtain ⟨C, _, _, hCet, τ, hτ, hτker⟩ :=
    etale_lift_along_surjection P (P ⧸ I) B Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (algebraMap P (P ⧸ I)) = I := Ideal.mk_ker
  rw [hker] at hτker
  let : Algebra k C := ((algebraMap P C).comp (algebraMap k P)).toAlgebra
  have : IsScalarTower k P C := .of_algebraMap_eq fun _ => rfl
  let φ : P →ₐ[k] C := { toRingHom := algebraMap P C, commutes' := fun _ => rfl }
  have hφ : φ.toRingHom.Etale := RingHom.etale_algebraMap.mpr hCet
  have hkerle : Ideal.map φ.toRingHom I ≤
      Ideal.comap (τ.restrictScalars k) (⊥ : Ideal B) := by
    change Ideal.map (algebraMap P C) I ≤ RingHom.ker τ.toRingHom
    exact hτker.symm.le
  let τbar : (C ⧸ Ideal.map φ.toRingHom I) →ₐ[k] B :=
    (AlgEquiv.quotientBot k B).toAlgHom.comp
      (Ideal.quotientMapₐ (⊥ : Ideal B) (τ.restrictScalars k) hkerle)
  have hτbar_mk (c : C) : τbar (Ideal.Quotient.mk _ c) = τ c := by
    change (AlgEquiv.quotientBot k B)
      (Ideal.quotientMapₐ (⊥ : Ideal B) (τ.restrictScalars k) hkerle
        (Ideal.Quotient.mk _ c)) = τ c
    rw [Ideal.quotient_map_mkₐ]
    change (AlgEquiv.quotientBot k B) (Ideal.Quotient.mk ⊥ (τ c)) = τ c
    rw [AlgEquiv.quotientBot_mk]
  have hτbar : Function.Surjective τbar := fun b => by
    obtain ⟨c, rfl⟩ := hτ b
    exact ⟨Ideal.Quotient.mk _ c, hτbar_mk c⟩
  have hcomm (x : P) : τbar (Ideal.Quotient.mk (Ideal.map φ.toRingHom I) (φ x)) =
      algebraMap (P ⧸ I) B (Ideal.Quotient.mk I x) :=
    calc
      _ = τ (φ x) := hτbar_mk _
      _ = algebraMap P B x := by simp [φ]
      _ = _ := rfl
  obtain ⟨ψ, hψ, hNF, τbar', hτbar', hcomm'⟩ :=
    exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero
      k p hp n I B C φ hφ τbar hτbar hcomm
  have hψft : ψ.toRingHom.FiniteType := by
    let : Algebra P C := ψ.toRingHom.toAlgebra
    have : Algebra.Etale P C := hψ.toAlgebra
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  exact ⟨C, inferInstance, ψ.toRingHom,
    τbar'.toRingHom.comp (Ideal.Quotient.mk (Ideal.map ψ.toRingHom I)), hψ,
    finite_of_nonfiniteGeneratorNumber_eq_zero _ hψft hNF,
    hτbar'.comp Ideal.Quotient.mk_surjective, RingHom.ext fun x => hcomm' x⟩

/-- In positive characteristic, a finite étale algebra `B` over a quotient `A` of
`k[x₁, …, xₙ]` is a quotient of a finite étale `k[x₁, …, xₙ]`-algebra over `A`. -/
private theorem exists_finite_etale_surjection_of_surjective
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ) {A B : Type u}
    [CommRing A] [CommRing B] (α : MvPolynomial (Fin n) k →+* A) (hα : Function.Surjective α)
    (β : A →+* B) (hβ : β.Etale) (hβf : β.Finite) :
    ∃ (C : Type u) (_ : CommRing C) (ψ : MvPolynomial (Fin n) k →+* C) (τ₀ : C →+* B),
      ψ.Etale ∧ ψ.Finite ∧ Function.Surjective τ₀ ∧ τ₀.comp ψ = β.comp α := by
  let P := MvPolynomial (Fin n) k
  let I : Ideal P := RingHom.ker α
  let A₀ := P ⧸ I
  let e : A₀ ≃+* A := RingHom.quotientKerEquivOfSurjective hα
  let : Algebra A B := β.toAlgebra
  have : Module.Finite A B := hβf
  let : Algebra k A₀ := Ideal.Quotient.algebra k
  let : Algebra A₀ A := e.toRingHom.toAlgebra
  let : Algebra A₀ B := (β.comp e.toRingHom).toAlgebra
  have : IsScalarTower A₀ A B := .of_algebraMap_eq fun _ => rfl
  let : Algebra k B := ((β.comp α).comp (algebraMap k P)).toAlgebra
  let : SMul k A₀ := Algebra.toSMul
  have : IsScalarTower k A₀ B := .of_algebraMap_eq (fun x => by
    change (β.comp α) ((algebraMap k P) x) =
      (β.comp e.toRingHom) ((algebraMap k A₀) x)
    rw [← Ideal.Quotient.mk_algebraMap k I x]
    exact (congrArg β (RingHom.quotientKerEquivOfSurjective_apply_mk hα
      (algebraMap k P x))).symm)
  have : Algebra.Etale A₀ B := (RingHom.Etale.respectsIso.2 β e hβ).toAlgebra
  have : Module.Finite A₀ A := inferInstance
  have : Module.Finite A₀ B := .trans A B
  obtain ⟨C, _, ψ, τ₀, hψ, hψf, hτ₀, h⟩ := exists_finite_etale_surjection_of_quotient k p hp n I B
  exact ⟨C, inferInstance, ψ, τ₀, hψ, hψf, hτ₀, h.trans <| RingHom.ext fun x =>
    congrArg β (RingHom.quotientKerEquivOfSurjective_apply_mk hα x)⟩

end Stacks.Etale

namespace AlgebraicGeometry

/-- A morphism `i : Z ⟶ Spec R` from an affine scheme factors as `Z ≅ Spec Γ(Z, ⊤)` followed by
the spectrum of the ring map `R ⟶ Γ(Z, ⊤)` it induces. -/
private theorem isoSpec_hom_comp_Spec_map_ΓSpecIso_inv_comp_appTop {R : CommRingCat.{u}}
    {Z : Scheme.{u}} [IsAffine Z] (i : Z ⟶ Spec R) :
    Z.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ i.appTop) = i :=
  calc
    _ = (Z.isoSpec.hom ≫ Spec.map i.appTop) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
          rw [Spec.map_comp, Category.assoc]
    _ = (i ≫ (Spec R).isoSpec.hom) ≫ (Spec R).isoSpec.inv := by
          rw [Scheme.isoSpec_hom_naturality i, Scheme.isoSpec_Spec_inv]
    _ = i := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Stacks Project, Tag 0G1H.** In positive characteristic, a finite étale cover of a closed
subscheme of affine space is an open-and-closed part of the restriction of a finite étale cover
of affine space. -/
@[stacks 0G1H]
theorem exists_finiteEtale_openClosed_pullback
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ)
    {Z : Scheme.{u}}
    (i : Z ⟶ Spec (.of (MvPolynomial (Fin n) k))) [IsClosedImmersion i]
    {Y : Scheme.{u}} (g : Y ⟶ Z) [IsFinite g] [Etale g] :
    ∃ (U : Scheme.{u}) (f : U ⟶ Spec (.of (MvPolynomial (Fin n) k)))
      (_ : IsFinite f) (_ : Etale f)
      (j : Y ⟶ pullback f i),
      IsOpenImmersion j ∧ IsClosedImmersion j ∧
        j ≫ pullback.snd f i = g := by
  let P := MvPolynomial (Fin n) k
  have : IsAffineHom i :=
    (isClosedImmersion_iff_isAffineHom.mp (inferInstance : IsClosedImmersion i)).1
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : IsAffine Y := isAffine_of_isAffineHom g
  let α := ((Scheme.ΓSpecIso (.of P)).inv ≫ i.appTop).hom
  have hα : Function.Surjective α :=
    (Scheme.Hom.app_surjective i ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of P)).inv).2
  let β := g.appTop.hom
  obtain ⟨C, _, ψ, τ₀, hψ, hψf, hτ₀, hτcompat⟩ :=
    Stacks.Etale.exists_finite_etale_surjection_of_surjective k p hp n α hα β
      (by simpa [β, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        g.etale_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp))
      (by simpa [β] using g.finite_appTop)
  let f : Spec (.of C) ⟶ Spec (.of P) := Spec.map (CommRingCat.ofHom ψ)
  have hfinitef : IsFinite f := (IsFinite.SpecMap_iff _).mpr hψf
  have hetalef : Etale f := (HasRingHomProperty.Spec_iff).mpr hψ
  let q : Y ⟶ Spec (.of C) := Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom τ₀)
  have hqclosed : IsClosedImmersion q := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom τ₀)) :=
      IsClosedImmersion.spec_of_surjective _ hτ₀
    dsimp [q]
    infer_instance
  have hfactor : q ≫ f = g ≫ i := by
    have hβscheme : Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom β) = g ≫ Z.isoSpec.hom := by
      simpa [β] using Scheme.isoSpec_hom_naturality g
    have hαscheme : Z.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom α) = i :=
      isoSpec_hom_comp_Spec_map_ΓSpecIso_inv_comp_appTop i
    calc
      q ≫ f = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (τ₀.comp ψ)) := by
        rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      _ = (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom β)) ≫ Spec.map (CommRingCat.ofHom α) := by
        rw [hτcompat, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      _ = g ≫ i := by rw [hβscheme, Category.assoc, hαscheme]
  let j : Y ⟶ pullback f i := pullback.lift q g hfactor
  have hjsnd : j ≫ pullback.snd f i = g := pullback.lift_snd _ _ _
  have : Etale (j ≫ pullback.snd f i) := by
    rw [hjsnd]
    infer_instance
  have : Etale j := Etale.of_comp j (pullback.snd f i)
  have hjclosed : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f i) := by
      simpa only [j, pullback.lift_fst] using hqclosed
    exact IsClosedImmersion.of_comp j (pullback.fst f i)
  have : Mono j := by
    rw [IsClosedImmersion.iff_isFinite_and_mono] at hjclosed
    exact hjclosed.2
  exact ⟨_, f, hfinitef, hetalef, j, isOpenImmersion_of_etale_universallyInjective j, hjclosed,
    hjsnd⟩

end AlgebraicGeometry

end
