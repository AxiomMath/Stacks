module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient

/-!
# Localizing a module over a quotient ring at a prime of the quotient

Let `A` be a ring, `J ⊆ A` an ideal, `π : A → A ⧸ J` the quotient map, and `𝔮` a prime of
`A ⧸ J`.  Write `𝔭 = π⁻¹(𝔮)`, a prime of `A` containing `J`, and `A_𝔭` for the localization of
`A` at `𝔭`.  For an `A ⧸ J`-module `N` there are two localizations in sight:

* `N` localized at `𝔮` as an `A ⧸ J`-module, a module over `Localization.AtPrime 𝔮`, and
* `N` localized at `𝔭` as an `A`-module through `π`, a module over `A_𝔭`.

They agree, because the complement of `𝔮` is the image under `π` of the complement of `𝔭`; and
the ring `A_𝔭 / J A_𝔭` is itself a localization of `A ⧸ J` at `𝔮`, so it is isomorphic to
`Localization.AtPrime 𝔮` as an `A ⧸ J`-algebra.  Together these identifications turn a finite
free `A_𝔭 / J A_𝔭`-module structure on the `𝔭`-localization of `N` into a free
`Localization.AtPrime 𝔮`-module structure on the `𝔮`-localization of `N`.

## Main results

* `Module.free_localizedModule_atPrime_of_quotient`: if the `𝔭`-localization of `N` is a finite
  free `A_𝔭 / J A_𝔭`-module, then the `𝔮`-localization of `N` is a free
  `Localization.AtPrime 𝔮`-module.
* `Ideal.not_le_comap_of_notMem_map`: an ideal `a` of `A` is not contained in `π⁻¹(𝔮)` as soon as
  the image `π(a)` contains an element outside `𝔮`.

## Implementation notes

The identification of the two localizations of `N` is obtained from
`IsLocalizedModule.restrictScalars`: the image of `𝔭ᶜ` in `A ⧸ J` is `𝔮ᶜ`, so the canonical
`A ⧸ J`-linear map from `N` to its `𝔮`-localization is, after restriction of scalars to `A`, a
localization at `𝔭ᶜ`.  The resulting comparison map is only `A`-linear; it is upgraded to
`A ⧸ J`-linearity using surjectivity of `π`, and then to `Localization.AtPrime 𝔮`-linearity using
`LinearEquiv.extendScalarsOfIsLocalization`.
-/

@[expose] public section

universe u

namespace Ideal

/-- An ideal `a` of `A` is not contained in the contraction of `q ⊆ A ⧸ J` along the quotient map
as soon as the image of `a` in `A ⧸ J` contains an element outside `q`. -/
theorem not_le_comap_of_notMem_map {A : Type u} [CommRing A] {J a : Ideal A}
    {q : Ideal (A ⧸ J)} {g : A ⧸ J} (hg : g ∈ a.map (Ideal.Quotient.mk J)) (hgq : g ∉ q) :
    ¬ a ≤ q.comap (Ideal.Quotient.mk J) :=
  fun h ↦ hgq (Ideal.map_le_iff_le_comap.mpr h hg)

end Ideal

/-- The image in `A ⧸ J` of the complement of the contraction of a prime `q ⊆ A ⧸ J` is the
complement of `q`.  This is the submonoid-level statement behind the identification of the
localization of an `A ⧸ J`-module at `q` with its localization at the contraction of `q`. -/
private theorem algebraMapSubmonoid_primeCompl_comap {A : Type u} [CommRing A] (J : Ideal A)
    (q : Ideal (A ⧸ J)) [q.IsPrime] :
    Algebra.algebraMapSubmonoid (A ⧸ J) (q.comap (Ideal.Quotient.mk J)).primeCompl =
      q.primeCompl := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨fun ⟨z, hz, hzy⟩ hmem ↦ hz ?_, fun hx ↦ ⟨y, hx, rfl⟩⟩
  have hzz : (Ideal.Quotient.mk J) z = (Ideal.Quotient.mk J) y := by
    simpa [Ideal.Quotient.algebraMap_eq] using hzy
  simpa [Ideal.mem_comap, hzz] using hmem

/-- An `A`-linear equivalence between two `B`-modules whose `A`-actions are the restrictions of
their `B`-actions is `B`-linear, provided the structure map `A → B` is surjective: every scalar
in `B` is the image of one in `A`. -/
private def linearEquivOfSurjectiveAlgebraMap {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A B)) {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module B X] [IsScalarTower A B X]
    [Module A Y] [Module B Y] [IsScalarTower A B Y] (g : X ≃ₗ[A] Y) : X ≃ₗ[B] Y where
  toFun := g
  map_add' := g.map_add
  map_smul' b x := by
    obtain ⟨a, rfl⟩ := hsurj b
    simpa only [RingHom.id_apply, IsScalarTower.algebraMap_smul] using g.map_smul a x
  invFun := g.symm
  left_inv := g.left_inv
  right_inv := g.right_inv

/-- The content of `Module.free_localizedModule_atPrime_of_quotient`, stated for a bare module
carrying compatible `A`- and `A ⧸ J`-module structures. -/
private theorem free_localizedModule_atPrime_of_quotient_aux {A : Type u} [CommRing A]
    (J : Ideal A) (M : Type u) [AddCommGroup M] [Module (A ⧸ J) M] [Module A M]
    [IsScalarTower A (A ⧸ J) M] (q : Ideal (A ⧸ J)) [q.IsPrime] (r : ℕ)
    (e : LocalizedModule (q.comap (Ideal.Quotient.mk J)).primeCompl M
        ≃ₗ[Localization.AtPrime (q.comap (Ideal.Quotient.mk J))]
        (Fin r → (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)) ⧸
          J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))))))) :
    Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M) := by
  -- The `A`-action on the `𝔮`-localization of `M` is the restriction of its `A ⧸ J`-action.
  have htower : IsScalarTower A (A ⧸ J) (LocalizedModule q.primeCompl M) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      rw [Algebra.algebraMap_eq_smul_one]
      exact OreLocalization.smul_one_smul a x
  -- The `𝔮`-localization is also the `𝔭`-localization, since `𝔮ᶜ` is the image of `𝔭ᶜ`.
  have himage : IsLocalizedModule (Algebra.algebraMapSubmonoid (A ⧸ J)
      (q.comap (Ideal.Quotient.mk J)).primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl M) := by
    rw [algebraMapSubmonoid_primeCompl_comap]
    infer_instance
  have := IsLocalizedModule.restrictScalars (A := A ⧸ J)
    (q.comap (Ideal.Quotient.mk J)).primeCompl (LocalizedModule.mkLinearMap q.primeCompl M)
  -- `A_𝔭 / J A_𝔭` is a localization of `A ⧸ J` at `𝔮`, hence isomorphic to
  -- `Localization.AtPrime 𝔮`.
  have : IsLocalization.AtPrime
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)) ⧸
        J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))))) q :=
    isLocalization_atPrime_quotient _ _ J q rfl
  have hsurj : Function.Surjective (algebraMap A (A ⧸ J)) := Ideal.Quotient.mk_surjective
  exact Module.Free.of_equiv (LinearEquiv.extendScalarsOfIsLocalization q.primeCompl
    (Localization.AtPrime q) (LinearEquiv.trans
      (LinearEquiv.piCongrRight fun _ : Fin r ↦
        (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
          (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)) ⧸
            J.map (algebraMap A
              (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)))))).toLinearEquiv)
      (linearEquivOfSurjectiveAlgebraMap hsurj
        (LinearEquiv.trans (e.restrictScalars A).symm
          (IsLocalizedModule.linearEquiv (q.comap (Ideal.Quotient.mk J)).primeCompl
            (LocalizedModule.mkLinearMap (q.comap (Ideal.Quotient.mk J)).primeCompl M)
            ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars A))))))

/-- **Freeness of the localization of a module over a quotient ring.** Let `J` be an ideal of `A`,
let `N` be an `A ⧸ J`-module, let `q` be a prime of `A ⧸ J` and let `p = q.comap π` be its
contraction along the quotient map `π : A → A ⧸ J`.  If localizing `N` at `p`, as an `A`-module
through `π`, produces a finite free module over `A_p / J A_p`, then localizing `N` at `q`, as an
`A ⧸ J`-module, produces a free module over `Localization.AtPrime q`.

The two localizations of `N` agree because the complement of `q` is the image of the complement
of `p`, and `A_p / J A_p` is a localization of `A ⧸ J` at `q`. -/
theorem Module.free_localizedModule_atPrime_of_quotient {A : Type u} [CommRing A] (J : Ideal A)
    (N : ModuleCat.{u} (A ⧸ J)) (q : Ideal (A ⧸ J)) [q.IsPrime] (r : ℕ)
    (e : LocalizedModule (q.comap (Ideal.Quotient.mk J)).primeCompl
          (((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj N) : Type u)
        ≃ₗ[Localization.AtPrime (q.comap (Ideal.Quotient.mk J))]
        (Fin r → (Localization.AtPrime (q.comap (Ideal.Quotient.mk J)) ⧸
          J.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk J))))))) :
    Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl (N : Type u)) := by
  let : Module A (N : Type u) := Module.compHom _ (Ideal.Quotient.mk J)
  have : IsScalarTower A (A ⧸ J) (N : Type u) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact free_localizedModule_atPrime_of_quotient_aux J (N : Type u) q r e

end
