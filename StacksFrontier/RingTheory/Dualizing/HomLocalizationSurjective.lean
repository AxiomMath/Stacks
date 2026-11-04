module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coextension of scalars along a surjection commutes with localization

Let `A → B` be a surjection of commutative rings with `A` Noetherian, let `q` be a prime of `B`
and let `p` be its contraction to `A`. Because the surjection carries the complement of `p` onto
the complement of `q`, the local ring `B_q` is simultaneously the localization of `B` at `q` and
the localization of the `A`-module `B` at `p`; in particular `B_q = B ⊗_A A_p`. Since `B` is a
finitely presented `A`-module — it is a finite `A`-module and `A` is Noetherian — forming
`Hom_A(B, -)` commutes with that localization: for every `A`-module `M` the canonical map

`A_p ⊗_A Hom_A(B, M) ⟶ Hom_{A_p}(B_q, A_p ⊗_A M)`,

sending `1 ⊗ φ` to the unique `A_p`-linear map taking the image of `b` to `1 ⊗ φ b`, is an
isomorphism. This is the module-level content of the comparison of derived Hom with flat base
change in the case of a finite surjection: `RHom_A(B, -)` is the derived functor of
`Hom_A(B, -) = `coextension of scalars, and the comparison above, applied degreewise to a
bounded complex of injectives representing a dualizing complex `K`, is the statement that
`RHom_A(B, K)_q` and `RHom_{A_p}(B_q, K_p)` are computed by one and the same complex of
`B_q`-modules.

## Main results

* `Dualizing.map_primeCompl_comap_of_surjective` — a surjection carries the complement of the
  contraction of a prime onto the complement of that prime.
* `Dualizing.isLocalization_algebraMapSubmonoid_primeCompl` — consequently the local ring at a
  prime of the quotient is the localization of the quotient at the image of the complement of
  the contracted prime.
* `Dualizing.exists_linearEquiv_hom_localization_of_surjective` — for a surjection of
  commutative rings with Noetherian source, localizing `Hom_A(B, M)` at `p` gives
  `Hom_{A_p}(B_q, M_p)`, by the map sending `1 ⊗ φ` to the `A_p`-linear extension of `φ`.

## Implementation notes

The two localizations are arbitrary: `A_p` and `B_q` are hypotheses, characterized by
`IsLocalization` at the two prime complements and tied together by the scalar towers
`IsScalarTower A B B_q` and `IsScalarTower A A_p B_q`. The canonical choices
`Localization.AtPrime` satisfy all of these once the `A_p`-algebra structure on `B_q` induced by
the surjection is installed, and nothing below depends on which model is used.

The isomorphism is produced from uniqueness of localized modules rather than constructed by
hand: both `A_p ⊗_A Hom_A(B, M)` and `Hom_{A_p}(B_q, A_p ⊗_A M)` are localizations of
`Hom_A(B, M)` at the complement of `p` — the first because localization is a base change along
`A → A_p`, the second because `B` is finitely presented over `A` — so they are isomorphic by a
unique isomorphism compatible with the two localization maps. That compatibility is what the
displayed formula `1 ⊗ φ ↦ (image of b ↦ 1 ⊗ φ b)` records, and it is what pins the
isomorphism down: the equation determines it on the image of `Hom_A(B, M)`, and a map out of a
localization is determined there.

Finite presentation of `B` over `A` is read off the surjection: `B` is a finite `A`-module, and
over a Noetherian ring a finite module is finitely presented.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
-/

@[expose] public section

open TensorProduct

universe u v

namespace Dualizing

/-- **A surjection carries the complement of a contracted prime onto the complement of the
prime.** For a surjection `A → B` and a prime `q` of `B`, the image of the complement of the
contraction `p` of `q` is the complement of `q`: an element of `A` lies outside `p` exactly when
its image lies outside `q`, and every element of `B` is such an image. -/
theorem map_primeCompl_comap_of_surjective {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B) :
    (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl.map (algebraMap A B) =
      q.asIdeal.primeCompl := by
  ext b
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩ hq
    exact ha (by simpa using hq)
  · intro hb
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, fun ha => hb (by simpa using ha), rfl⟩

/-- **The local ring at a prime of a quotient is a localization of the quotient at the image of
the contracted prime complement.** This is `Dualizing.map_primeCompl_comap_of_surjective` read as
a statement about `IsLocalization`: the submonoid of `B` generated as the image of the complement
of `p` is the complement of `q`, so `B_q` is the localization of `B` at that image. It is the form
in which the `A`-module `B_q` is recognized as the localization of the `A`-module `B` at the
complement of `p`. -/
theorem isLocalization_algebraMapSubmonoid_primeCompl {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B)
    (Bq : Type u) [CommRing Bq] [Algebra B Bq] [IsLocalization q.asIdeal.primeCompl Bq] :
    IsLocalization
      (Algebra.algebraMapSubmonoid B
        (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl) Bq := by
  rw [Algebra.algebraMapSubmonoid, map_primeCompl_comap_of_surjective hf q]
  infer_instance

/-- **Hom out of a surjection commutes with localization at a prime.** Let `A → B` be a
surjection of commutative rings with `A` Noetherian, let `q` be a prime of `B` and `p` its
contraction, and let `A_p` and `B_q` be localizations of `A` at `p` and of `B` at `q`, compatibly
as `A`-algebras. Then for every `A`-module `M` the localization of `Hom_A(B, M)` at `p`, formed
as the base change `A_p ⊗_A Hom_A(B, M)`, is `Hom_{A_p}(B_q, A_p ⊗_A M)`, by the isomorphism
sending `1 ⊗ φ` to the `A_p`-linear map carrying the image of `b` in `B_q` to `1 ⊗ φ b`.

The displayed formula characterizes the isomorphism, since a map out of a localization is
determined by its restriction along the localization map; it is stated as part of the conclusion
for that reason. -/
@[ega "0 1.5.3" "special case"]
theorem exists_linearEquiv_hom_localization_of_surjective {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (hf : Function.Surjective (algebraMap A B)) (q : PrimeSpectrum B)
    (Ap Bq : Type u) [CommRing Ap] [CommRing Bq] [Algebra A Ap] [Algebra B Bq] [Algebra A Bq]
    [Algebra Ap Bq] [IsScalarTower A B Bq] [IsScalarTower A Ap Bq]
    [IsLocalization (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl Ap]
    [IsLocalization q.asIdeal.primeCompl Bq]
    (M : Type v) [AddCommGroup M] [Module A M] :
    ∃ e : TensorProduct A Ap (B →ₗ[A] M) ≃ₗ[A] (Bq →ₗ[Ap] TensorProduct A Ap M),
      ∀ (φ : B →ₗ[A] M) (b : B), e (1 ⊗ₜ[A] φ) (algebraMap B Bq b) = 1 ⊗ₜ[A] φ b := by
  have hS := isLocalization_algebraMapSubmonoid_primeCompl hf q Bq
  have hfin : Module.Finite A B := Module.Finite.of_surjective (Algebra.linearMap A B) hf
  have hfp : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  set S := (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.primeCompl
  have hB : IsLocalizedModule S ((Algebra.linearMap B Bq).restrictScalars A) :=
    IsLocalizedModule.restrictScalars _ (Algebra.linearMap B Bq)
  have hT : IsLocalizedModule S (TensorProduct.mk A Ap (B →ₗ[A] M) 1) :=
    IsLocalization.tensorProduct_isLocalizedModule _ Ap
  let g := IsLocalizedModule.mapExtendScalars S
    ((Algebra.linearMap B Bq).restrictScalars A) (TensorProduct.mk A Ap M 1) Ap
  refine ⟨IsLocalizedModule.linearEquiv S (TensorProduct.mk A Ap (B →ₗ[A] M) 1) g, fun φ b => ?_⟩
  exact (congrArg (fun z => z (algebraMap B Bq b))
    (IsLocalizedModule.linearEquiv_apply S (TensorProduct.mk A Ap (B →ₗ[A] M) 1) g φ)).trans
    (IsLocalizedModule.map_apply _ ((Algebra.linearMap B Bq).restrictScalars A)
      (TensorProduct.mk A Ap M 1) φ b)

end Dualizing

end
