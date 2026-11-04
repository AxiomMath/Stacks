module

public import StacksFrontier.AlgebraicGeometry.AffinePushforwardStalk.Normalization
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationOwnStalk
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.LeibnizStalkUnique
public import StacksFrontier.RingTheory.Derivation.Localization

/-!
# Two extensions of a vector field over two affine opens have the same germ

Let `X` be a scheme over a field `k` whose quasi-compact opens have finitely many irreducible
components, let `ν : X^ν ⟶ X` be its normalization and let `D` be a vector field on `X`. Over an
affine open `U` of `X` one may try to extend `D` to the sections of the normalization, that is, to
produce an additive map `E` of `Γ(X^ν, ν⁻¹U)` obeying the Leibniz rule and satisfying
`E (ν^♯ r) = ν^♯ (D r)` for every `r : Γ(X, U)`. Such an `E` is far from canonical as a map of
rings of sections, but this file shows that *germwise* it is: if `E` is such an extension over `U`
and `F` is one over `V`, and `x` lies in both, then `E` and `F` induce the same map on the stalk
`(ν_* 𝒪_{X^ν})_x`. In particular two sections with the same germ at `x` are sent to sections with
the same germ.

## Main results

* `Stacks.Curves.exists_leibniz_of_extension`: an extension of `D` over an affine open `U`
  containing `x` induces a Leibniz additive map of `(ν_* 𝒪_{X^ν})_x` computing germs of its
  values, and that map agrees on the image of `𝒪_{X, x}` with the map `D` induces there.
* `Stacks.Curves.germ_eq_of_extension_of_extension`: two extensions of a vector field over two
  affine opens agree germwise at any common point.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.NormalizationStalkAmbient
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

section ExtensionGerm

variable {X : Scheme.{u}}

/-- Let `ν : X^ν ⟶ X` be the normalization, let `U` be an affine open containing `x` and let `E`
be an additive map of `Γ(X^ν, ν⁻¹U)` obeying the Leibniz rule and extending the vector field `D`
along `ν^♯`. Then there is an additive map `g` of the stalk `(ν_* 𝒪_{X^ν})_x` which obeys the
Leibniz rule, sends the germ of `z` to the germ of `E z`, and agrees on the image of `𝒪_{X, x}`
with the map `D` induces on that local ring. -/
public theorem exists_leibniz_of_extension
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {hX : X ⟶ Spec (.of k)} (D : SheafDerivationOf hX)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    (E : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) →+
         Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U))
    (hEmul : ∀ z w, E (z * w) = z * E w + w * E z)
    (hEext : ∀ r : Γ(X, U),
      E (((Scheme.normalization X hfin).app U).hom r)
        = ((Scheme.normalization X hfin).app U).hom (D.onSections r)) :
    letI : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) :=
      normalizationPushforwardStalkAlgebra X hfin x
    ∃ g : normalizationPushforwardStalk X hfin x →+ normalizationPushforwardStalk X hfin x,
      (∀ z w, g (z * w) = z * g w + w * g z) ∧
      (∀ z, g (((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU z)
          = ((Scheme.normalization X hfin).base _*
            (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU (E z)) ∧
      ∀ a : X.presheaf.stalk x,
        g (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) a)
          = algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
              (ownStalkFun D a) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) :=
    ((Scheme.normalization X hfin).app U).hom.toAlgebra
  let : Algebra Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (normalizationPushforwardStalk X hfin x) :=
    (((Scheme.normalization X hfin).base _*
      (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) :=
    normalizationPushforwardStalkAlgebra X hfin x
  let : Algebra Γ(X, U) (normalizationPushforwardStalk X hfin x) :=
    ((algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)).comp
      (algebraMap Γ(X, U) (X.presheaf.stalk x))).toAlgebra
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x)
      (normalizationPushforwardStalk X hfin x) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hstalk : IsLocalization (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl
      (X.presheaf.stalk x) := hU.isLocalization_stalk (⟨x, hxU⟩ : U)
  have hpush : IsLocalization (Algebra.algebraMapSubmonoid
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl)
      (normalizationPushforwardStalk X hfin x) :=
    isLocalization_normalizationPushforwardStalk X hfin hU hxU
  have hcomp : ∀ r : Γ(X, U),
      algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
          (X.presheaf.germ U x hxU r)
        = algebraMap Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
            (normalizationPushforwardStalk X hfin x)
            (((Scheme.normalization X hfin).app U).hom r) := fun r ↦
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU (Scheme.normalization X hfin).c r
  let ι : X.presheaf.stalk x →+ normalizationPushforwardStalk X hfin x :=
    AddMonoidHom.mk' (fun a ↦ algebraMap (X.presheaf.stalk x)
      (normalizationPushforwardStalk X hfin x) a) fun a b ↦ map_add _ a b
  have crux : ∀ g : normalizationPushforwardStalk X hfin x →+
        normalizationPushforwardStalk X hfin x,
      (∀ z w, g (z * w) = z * g w + w * g z) →
      (∀ z : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U),
        g (algebraMap Γ(Scheme.normalizationScheme X hfin,
              Scheme.normalization X hfin ⁻¹ᵁ U)
            (normalizationPushforwardStalk X hfin x) z)
          = algebraMap Γ(Scheme.normalizationScheme X hfin,
              Scheme.normalization X hfin ⁻¹ᵁ U)
            (normalizationPushforwardStalk X hfin x) (E z)) →
      ∀ a : X.presheaf.stalk x,
        g (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) a)
          = algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
              (ownStalkFun D a) := by
    intro g hgmul hgext a
    have hg1 : g 1 = 0 := by simpa using hgmul 1 1
    let mkD : ∀ f : X.presheaf.stalk x →+ normalizationPushforwardStalk X hfin x,
        (∀ p q, f (p * q) = p • f q + q • f p) →
        Derivation ℤ (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x) :=
      fun f hf ↦ { toLinearMap := f.toIntLinearMap
                   map_one_eq_zero' := by simpa using hf 1 1
                   leibniz' := hf }
    let d₁ := mkD (g.comp ι) fun p q ↦ by
      simp only [AddMonoidHom.comp_apply, ι, AddMonoidHom.mk'_apply, map_mul, hgmul,
        Algebra.smul_def]
    let d₂ := mkD (ι.comp (ownStalkAddHom D x)) fun p q ↦ by
      change algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
            (ownStalkFun D (p * q)) = _
      rw [ownStalkFun_mul, map_add, map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
      rfl
    have hd : d₁ = d₂ := by
      refine Stacks.DerivationExtension.derivation_ext_of_algebraMap_of_tower
        (S := (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl) d₁ d₂ fun r ↦ ?_
      change g (algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
            (algebraMap Γ(X, U) (X.presheaf.stalk x) r))
        = algebraMap (X.presheaf.stalk x) (normalizationPushforwardStalk X hfin x)
            (ownStalkFun D (algebraMap Γ(X, U) (X.presheaf.stalk x) r))
      have hr : algebraMap Γ(X, U) (X.presheaf.stalk x) r = X.presheaf.germ U x hxU r := rfl
      rw [hr, hcomp r, hgext, hEext r, ownStalkFun_germ D U hxU r, hcomp (D.onSections r)]
    exact DFunLike.congr_fun hd a
  have hm := Stacks.DerivationExtension.locLeibnizHom_mul E hEmul
    (Algebra.algebraMapSubmonoid
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl)
    (normalizationPushforwardStalk X hfin x)
  have hg := Stacks.DerivationExtension.locLeibnizHom_algebraMap E hEmul
    (Algebra.algebraMapSubmonoid
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U)
      (hU.primeIdealOf (⟨x, hxU⟩ : U)).asIdeal.primeCompl)
    (normalizationPushforwardStalk X hfin x)
  exact ⟨_, hm, hg, crux _ hm hg⟩

/-- Let `X` be a reduced scheme over `k` whose quasi-compact opens have finitely many irreducible
components, let `ν : X^ν ⟶ X` be its normalization and let `D` be a vector field on `X`. Suppose
`E` extends `D` to the sections of the normalization over the preimage of an affine open `U`, and
`F` does the same over an affine open `V`, both being additive and obeying the Leibniz rule. If
`x` lies in both `U` and `V` and sections `s` over `ν⁻¹U` and `t` over `ν⁻¹V` have the same germ
at `x`, then `E s` and `F t` have the same germ at `x`. -/
public theorem germ_eq_of_extension_of_extension [IsReduced X]
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {hX : X ⟶ Spec (.of k)} (D : SheafDerivationOf hX)
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (E : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) →+
         Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U))
    (hEmul : ∀ z w, E (z * w) = z * E w + w * E z)
    (hEext : ∀ r : Γ(X, U),
      E (((Scheme.normalization X hfin).app U).hom r)
        = ((Scheme.normalization X hfin).app U).hom (D.onSections r))
    (F : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ V) →+
         Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ V))
    (hFmul : ∀ z w, F (z * w) = z * F w + w * F z)
    (hFext : ∀ r : Γ(X, V),
      F (((Scheme.normalization X hfin).app V).hom r)
        = ((Scheme.normalization X hfin).app V).hom (D.onSections r))
    {x : X} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U))
    (t : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ V))
    (hst : ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU s
        = ((Scheme.normalization X hfin).base _*
          (Scheme.normalizationScheme X hfin).presheaf).germ V x hxV t) :
    ((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).germ U x hxU (E s)
      = ((Scheme.normalization X hfin).base _*
        (Scheme.normalizationScheme X hfin).presheaf).germ V x hxV (F t) := by
  obtain ⟨gU, hgUmul, hgUgerm, hgUalg⟩ :=
    exists_leibniz_of_extension hfin D hU hxU E hEmul hEext
  obtain ⟨gV, hgVmul, hgVgerm, hgValg⟩ :=
    exists_leibniz_of_extension hfin D hV hxV F hFmul hFext
  have hUV : gU = gV :=
    Stacks.AlgebraicGeometry.NormalizationQuotient.eq_of_leibniz_normalizationPushforwardStalk
      X hfin x gU gV hgUmul hgVmul fun a ↦ by rw [hgUalg a, hgValg a]
  rw [← hgUgerm s, hst, hUV, hgVgerm]

end ExtensionGerm

end Stacks.Curves

end
