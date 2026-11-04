module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.NormTrace
public import StacksFrontier.AlgebraicGeometry.Morphisms.GeometricComponents
public import StacksFrontier.FieldTheory.IntegralPrimitiveElement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite étale algebras from a separable residue extension, after shrinking the base

Let `R` be a ring, `p` a prime of `R` and `f : R[X]` monic. Stacks 0551 needs the morphism
`Spec (R[x]/(f)) → Spec R` to be *finite étale and surjective* over a neighbourhood of `p`, not
merely étale at the single prime cut out by a chosen root. The pieces assembled here are:

* an upgrade of `Stacks.GeometricComponents.isEtaleAt_of_liesOver` whose separability hypothesis is
  taken over the residue *field* `κ(p)` rather than over the residue *ring* `R ⧸ p`;
* the resulting "shrink the base" statement for `R[x]/(f)`, together with the monic polynomial
  over `R` that presents a given finite separable extension of `κ(p)`; and
* the transport of finiteness, freeness, étaleness and surjectivity from the pair
  `R → R[x]/(f)` to the pair `Rₕ → Bₕ` obtained by inverting `h` on both sides, which is the
  form in which the scheme-level argument of Stacks 0551 consumes them.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.GeometricComponents.isEtaleAt_of_liesOver_residueField`: if the image of a monic
  `f : R[X]` in `κ(p)[X]` is coprime to its derivative, then `R[x]/(f)` is étale over `R` at every
  prime lying over `p`.
* `Stacks.GeometricComponents.exists_notMem_etale_localizationAway_adjoinRoot_residueField`: the
  same hypothesis makes `R[x]/(f)` étale over `R` after inverting a single element outside `p`.
* `Stacks.GeometricComponents.exists_monic_map_eq_minpoly_residueField`: a finite separable
  extension `L` of `κ(p)` is presented by a monic polynomial over `R`.
* `Stacks.GeometricComponents.exists_monic_notMem_etale_localizationAway_residueField`: the two
  previous results combined, which is the ring-theoretic input of Stacks 0551.
* `Stacks.GeometricComponents.finite_isLocalization_adjoinRoot`,
  `free_isLocalization_adjoinRoot`, `etale_isLocalization_adjoinRoot`: for `Rₕ` a localization of
  `R` away from `h` and `Bₕ` the matching localization of `R[x]/(f)`, the algebra `Bₕ` is finite
  free over `Rₕ`, and étale as soon as `R[x]/(f)` is étale over `R` away from `h`.
* `Stacks.GeometricComponents.comap_surjective_isLocalization_adjoinRoot`: and then
  `Spec Bₕ → Spec Rₕ` is surjective.

## Implementation notes

`isEtaleAt_of_liesOver` takes its Bézout identity in `(R ⧸ p)[X]`, which is strictly stronger than
separability over `κ(p)` and is therefore not what Stacks 0551 has in hand: there the separable
extension `K'/K` is produced by Tag 054R over the function field `K = κ(√(0))`, and only a Bézout
identity over `K` is available. The upgrade costs one change of ambient ring: a prime `q` of
`R[x]/(f)` lying over `p` makes `R ⧸ p → (R[x]/(f)) ⧸ q` injective into a domain, hence induces
`κ(p) → Frac((R[x]/(f)) ⧸ q)`, and the Bézout identity is evaluated there instead. No localization
of `R` is needed, and in particular the reduction of `f` need not become separable over any
residue ring.

The localized statements are phrased for an arbitrary pair of localizations `Rₕ`, `Bₕ` with the
scalar towers, rather than for `Localization.Away`, so that they apply to the sections of a basic
open of an affine scheme without transporting along a comparison isomorphism. Étaleness is
transported by `Algebra.Etale.of_restrictScalars`: both `Rₕ` and `Bₕ` are étale over `R`, the
former because inverting an element is étale and the latter by hypothesis, so `Rₕ → Bₕ` is étale.

## References

* [Stacks Project, Tag 0551](https://stacks.math.columbia.edu/tag/0551)
* [Stacks Project, Tag 00UD](https://stacks.math.columbia.edu/tag/00UD)
-/

@[expose] public section

open Polynomial

universe u v

namespace Stacks.GeometricComponents

/-- **`R[x]/(f)` is étale over the fibre at `p` when `f` is separable over `κ(p)`.** If the image
of a monic `f : R[X]` in `κ(p)[X]` is coprime to its derivative, then `R[x]/(f)` is étale over `R`
at every prime lying over `p`.

This is `Stacks.GeometricComponents.isEtaleAt_of_liesOver` with its hypothesis weakened from the
residue ring `R ⧸ p` to the residue field `κ(p)`, which is the form in which separability of a
finite separable extension of `κ(p)` is available. A prime `q` lying over `p` makes
`R ⧸ p → (R[x]/(f)) ⧸ q` an injection into a domain, so it extends to `κ(p)` on the source and to
the fraction field on the target; evaluating a Bézout identity `u f + v f' = 1` of `κ(p)[X]` there
at the image of the root, where both `f` and `f'` vanish, would give `0 = 1`. -/
public theorem isEtaleAt_of_liesOver_residueField {R : Type u} [CommRing R] {f : R[X]}
    (hf : f.Monic) (p : Ideal R) [p.IsPrime]
    (hsep : IsCoprime (f.map (algebraMap R p.ResidueField))
      (derivative (f.map (algebraMap R p.ResidueField))))
    (q : Ideal (AdjoinRoot f)) [q.IsPrime] [q.LiesOver p] :
    Algebra.IsEtaleAt R q := by
  refine isEtaleAt_of_derivative_notMem hf q fun hd => ?_
  set E := FractionRing (AdjoinRoot f ⧸ q)
  set σ : AdjoinRoot f →+* E :=
    (algebraMap (AdjoinRoot f ⧸ q) E).comp (Ideal.Quotient.mk q) with hσ
  have hσker : ∀ a : R, σ (algebraMap R (AdjoinRoot f) a) = 0 ↔ a ∈ p := by
    intro a
    rw [hσ, RingHom.comp_apply,
      map_eq_zero_iff _ (IsFractionRing.injective (AdjoinRoot f ⧸ q) E),
      Ideal.Quotient.eq_zero_iff_mem, q.over_def p, Ideal.under_def, Ideal.mem_comap]
  let j : R ⧸ p →+* E := Ideal.Quotient.lift p (σ.comp (algebraMap R (AdjoinRoot f)))
    (fun a ha => (hσker a).mpr ha)
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).mpr fun x hx => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hσker a).mp hx)
  let θ : p.ResidueField →+* E := IsFractionRing.lift hjinj
  have hθ : θ.comp (algebraMap R p.ResidueField) = σ.comp (algebraMap R (AdjoinRoot f)) := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R (R ⧸ p) p.ResidueField,
      IsFractionRing.lift_algebraMap]
    rfl
  set γ : E := σ (AdjoinRoot.root f) with hγ
  have key : ∀ g : R[X],
      eval₂ θ γ (g.map (algebraMap R p.ResidueField)) = σ (AdjoinRoot.mk f g) := by
    intro g
    rw [eval₂_map, hθ, hγ, ← Polynomial.hom_eval₂]
    congr 1
    rw [← AdjoinRoot.aeval_eq g]
    rfl
  obtain ⟨u, v, huv⟩ := hsep
  have h1 : eval₂ θ γ (f.map (algebraMap R p.ResidueField)) = 0 := by
    rw [key f, AdjoinRoot.mk_self, map_zero]
  have h2 : eval₂ θ γ (derivative (f.map (algebraMap R p.ResidueField))) = 0 := by
    rw [Polynomial.derivative_map, key, hσ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hd, map_zero]
  have hone := congrArg (eval₂ θ γ) huv
  simp only [eval₂_add, eval₂_mul, eval₂_one, h1, h2, mul_zero, add_zero] at hone
  exact zero_ne_one hone

/-- **`R[x]/(f)` becomes étale after inverting one element outside `p`, from separability over
`κ(p)`.** For monic `f : R[X]` whose image in `κ(p)[X]` is coprime to its derivative, there is an
`h ∉ p` such that `R[x]/(f)` localized away from `h` is étale over `R`. -/
public theorem exists_notMem_etale_localizationAway_adjoinRoot_residueField {R : Type u}
    [CommRing R] {f : R[X]} (hf : f.Monic) (p : Ideal R) [p.IsPrime]
    (hsep : IsCoprime (f.map (algebraMap R p.ResidueField))
      (derivative (f.map (algebraMap R p.ResidueField)))) :
    ∃ h ∉ p, Algebra.Etale R (Localization.Away (algebraMap R (AdjoinRoot f) h)) := by
  have := hf.finite_adjoinRoot
  exact exists_notMem_etale_localizationAway p fun q _ _ =>
    isEtaleAt_of_liesOver_residueField hf p hsep q

/-- **A monic polynomial over `R` presenting a finite separable extension of `κ(p)`.** For `L` a
finite separable extension of the residue field of a prime `p` of `R`, there is a monic
`f : R[X]` whose image in `κ(p)[X]` is the minimal polynomial of a primitive element of `L`.

The denominators are cleared over the domain `R ⧸ p` by
`Field.exists_integral_primitive_element_of_isFractionRing`, and the resulting polynomial over
`R ⧸ p` is lifted to `R` along the surjection `R → R ⧸ p`, which preserves monicity. -/
@[sga "3 XXIV 3.9.1" "partial"]
public theorem exists_monic_map_eq_minpoly_residueField {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (f : R[X]) (β : L), f.Monic ∧
      f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β ∧
      IntermediateField.adjoin p.ResidueField {β} = ⊤ := by
  obtain ⟨F, β, hFmonic, hFmap, hβ⟩ :=
    Field.exists_integral_primitive_element_of_isFractionRing (R := R ⧸ p)
      (K := p.ResidueField) (L := L)
  have hlifts : F ∈ Polynomial.lifts (Ideal.Quotient.mk p) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun _ => Ideal.Quotient.mk_surjective _
  obtain ⟨f, hfmap, -, hfmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hFmonic
  refine ⟨f, β, hfmonic, ?_, hβ⟩
  rw [IsScalarTower.algebraMap_eq R (R ⧸ p) p.ResidueField, ← Polynomial.map_map,
    Ideal.Quotient.algebraMap_eq, hfmap, hFmap]

/-- **The polynomial and the element to invert, from a finite separable residue extension.** For
`L` a finite separable extension of `κ(p)` there are a monic `f : R[X]` presenting `L` as in
`exists_monic_map_eq_minpoly_residueField` and an `h ∉ p` such that `R[x]/(f)` localized away from
`h` is étale over `R`.

This is the ring-theoretic input of Stacks 0551: `R[x]/(f)` is finite free over `R` by
`Polynomial.Monic.finite_adjoinRoot` and `Polynomial.Monic.free_adjoinRoot`, and inverting `h`
makes it étale, so after shrinking the base the morphism of spectra is finite étale. -/
@[ega "0 10.3.1.2" "special case", sga "3 XXIV 3.9.1" "special case"]
public theorem exists_monic_notMem_etale_localizationAway_residueField {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (L : Type v) [Field L] [Algebra p.ResidueField L]
    [Module.Finite p.ResidueField L] [Algebra.IsSeparable p.ResidueField L] :
    ∃ (f : R[X]) (β : L) (h : R), f.Monic ∧
      f.map (algebraMap R p.ResidueField) = minpoly p.ResidueField β ∧
      IntermediateField.adjoin p.ResidueField {β} = ⊤ ∧ h ∉ p ∧
      Algebra.Etale R (Localization.Away (algebraMap R (AdjoinRoot f) h)) := by
  obtain ⟨f, β, hfmonic, hfmap, hβ⟩ := exists_monic_map_eq_minpoly_residueField p L
  have hsep : IsCoprime (f.map (algebraMap R p.ResidueField))
      (derivative (f.map (algebraMap R p.ResidueField))) := by
    rw [hfmap]
    exact Algebra.IsSeparable.isSeparable p.ResidueField β
  obtain ⟨h, hh, he⟩ :=
    exists_notMem_etale_localizationAway_adjoinRoot_residueField hfmonic p hsep
  exact ⟨f, β, h, hfmonic, hfmap, hβ, hh, he⟩

section Localization

variable {R : Type u} [CommRing R] {f : R[X]} (h : R)
variable (Rₕ Bₕ : Type u) [CommRing Rₕ] [CommRing Bₕ]
  [Algebra R Rₕ] [Algebra (AdjoinRoot f) Bₕ] [Algebra R Bₕ] [Algebra Rₕ Bₕ]
  [IsScalarTower R Rₕ Bₕ] [IsScalarTower R (AdjoinRoot f) Bₕ]
  [IsLocalization.Away h Rₕ]
  [IsLocalization (Algebra.algebraMapSubmonoid (AdjoinRoot f) (Submonoid.powers h)) Bₕ]
include h

/-- Inverting `h` on both sides of the finite free algebra `R → R[x]/(f)` leaves it finite. -/
public theorem finite_isLocalization_adjoinRoot (hf : f.Monic) : Module.Finite Rₕ Bₕ :=
  have := hf.finite_adjoinRoot
  Module.Finite.of_isLocalization R (AdjoinRoot f) (Submonoid.powers h)

/-- Inverting `h` on both sides of the finite free algebra `R → R[x]/(f)` leaves it free: the
power basis of `R[x]/(f)` localizes to a basis. -/
public theorem free_isLocalization_adjoinRoot (hf : f.Monic) : Module.Free Rₕ Bₕ :=
  .of_basis ((AdjoinRoot.powerBasis' hf).basis.localizationLocalization Rₕ
    (Submonoid.powers h) Bₕ)

/-- **Étaleness descends to the localized base.** If `R[x]/(f)` localized away from the image of
`h` is étale over `R`, then it is étale over the localization `Rₕ` of `R` away from `h`.

Both `Rₕ` and `Bₕ` are étale over `R` — the former because inverting an element is étale, the
latter by hypothesis read through the uniqueness of localizations — so
`Algebra.Etale.of_restrictScalars` applies to the tower `R → Rₕ → Bₕ`. -/
public theorem etale_isLocalization_adjoinRoot
    (hE : Algebra.Etale R (Localization.Away (algebraMap R (AdjoinRoot f) h))) :
    Algebra.Etale Rₕ Bₕ := by
  have hBaway : IsLocalization.Away (algebraMap R (AdjoinRoot f) h) Bₕ := by
    show IsLocalization (Submonoid.powers (algebraMap R (AdjoinRoot f) h)) Bₕ
    rw [← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have e : Bₕ ≃ₐ[AdjoinRoot f] Localization.Away (algebraMap R (AdjoinRoot f) h) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R (AdjoinRoot f) h)) _ _
  have : Algebra.Etale R Bₕ := Algebra.Etale.of_equiv (e.symm.restrictScalars R)
  have : Algebra.Etale R Rₕ := Algebra.Etale.of_isLocalizationAway h
  exact Algebra.Etale.of_restrictScalars R Rₕ Bₕ

/-- **`Spec Bₕ → Spec Rₕ` is surjective.** A nontrivial finite free algebra is faithfully flat, and
a faithfully flat algebra is surjective on prime spectra. -/
public theorem comap_surjective_isLocalization_adjoinRoot (hf : f.Monic) [Nontrivial Bₕ] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap Rₕ Bₕ)) :=
  have := finite_isLocalization_adjoinRoot h Rₕ Bₕ hf
  have := free_isLocalization_adjoinRoot h Rₕ Bₕ hf
  PrimeSpectrum.comap_surjective_of_faithfullyFlat

end Localization

end Stacks.GeometricComponents

end
