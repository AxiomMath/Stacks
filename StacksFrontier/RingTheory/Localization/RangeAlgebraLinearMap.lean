module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Basic

/-!
# Localizing the image of the base ring of an algebra

Let `A → C` be a map of commutative rings, let `M` be a submonoid of `A`, let `R` be the
localization of `A` at `M` and let `S` be the localization of `C` at the image of `M`. The image
of `A` in `C` is the `A`-submodule `LinearMap.range (Algebra.linearMap A C)`, and this file says
that localizing it at `M` gives the image of `R` in `S`:

```
(LinearMap.range (Algebra.linearMap A C)).localized' R M _ =
  LinearMap.range (Algebra.linearMap R S)
```

In other words, the formation of the image of the base ring commutes with localization. For
`C = A` this is `Ideal.localized'_eq_map` applied to `⊤`; the content here is that the module
being localized, `C`, is not the base ring.

The point of the statement is that it turns a question about the `A`-module `C / A` — for
instance about the conductor of `A` in its integral closure `A' = C` — into a question that may
be answered one maximal ideal at a time, through
`Submodule.eq_of_localization_maximal` and the rest of that family: those lemmas compare the
`localized'` of two submodules of `C`, and this file identifies the `localized'` of the image of
`A` with the image of a local ring, which is where the local computations live.

## Main results

* `Submodule.localized₀_range_algebraLinearMap`: the `localized₀` form, a submodule of `S` over
  the unlocalized `A`.
* `Submodule.localized'_range_algebraLinearMap`: the `localized'` form, a submodule of `S` over
  `R`.
* `Submodule.localized'_sup_smul_top_range_algebraLinearMap`: the image of `A` enlarged by
  `I • ⊤` for an ideal `I` of `A`, which is the shape the conductor statements of Stacks 0E68
  are stated in.

## Implementation notes

The localization map `C → S` is `(IsScalarTower.toAlgHom A C S).toLinearMap`, which is the
spelling under which Mathlib provides the instance
`IsLocalizedModule M (IsScalarTower.toAlgHom A C S).toLinearMap` from
`IsLocalization (Algebra.algebraMapSubmonoid C M) S`; since `localized'` mentions the
localization map, that spelling has to appear in the statement.

The proof is Mathlib's `LinearMap.range_localizedMap_eq_localized₀_range`, which computes the
localization of the range of any `A`-linear map as the range of the localized map, together with
the identification of the localized map of `Algebra.linearMap A C` with `Algebra.linearMap R S`.
That identification is a computation on a single fraction: two localization maps agree once they
agree on the image of `A`, by `IsLocalizedModule.linearMap_ext`, and on `1` both give `1`.

The hypotheses are left as instance binders rather than being specialized to
`R = Localization M` and `S = Localization (Algebra.algebraMapSubmonoid C M)`, because the
algebra structure on `R → S` arises in practice as `localizationAlgebra`, which is not an
instance for an arbitrary `Localization.AtPrime`.
-/

@[expose] public section

namespace Submodule

variable {A C R S : Type*} [CommRing A] [CommRing C] [CommRing R] [CommRing S]
  [Algebra A C] [Algebra A R] [Algebra C S] [Algebra R S] [Algebra A S]
  [IsScalarTower A R S] [IsScalarTower A C S]
  (M : Submonoid A) [IsLocalization M R]
  [IsLocalization (Algebra.algebraMapSubmonoid C M) S]

/-- The localized map of the structure map `A → C` is the structure map `R → S` of the
localizations. -/
theorem isLocalizedModule_map_algebraLinearMap :
    IsLocalizedModule.map M (Algebra.linearMap A R)
        (IsScalarTower.toAlgHom A C S).toLinearMap (Algebra.linearMap A C)
      = (Algebra.linearMap R S).restrictScalars A := by
  refine IsLocalizedModule.linearMap_ext M (Algebra.linearMap A R)
    (IsScalarTower.toAlgHom A C S).toLinearMap ?_
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Algebra.linearMap_apply]
  rw [show algebraMap A R a = IsLocalizedModule.mk' (Algebra.linearMap A R) a (1 : M) from
    (IsLocalizedModule.mk'_one M (Algebra.linearMap A R) a).symm, IsLocalizedModule.map_mk']
  simp only [IsLocalizedModule.mk'_one, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
    Algebra.linearMap_apply]
  rw [← IsScalarTower.algebraMap_apply A C S, ← IsScalarTower.algebraMap_apply A R S]

/-- **Localizing the image of the base ring**, `localized₀` form: the localization at `M` of the
image of `A` in `C` is the image of `R` in `S`, as an `A`-submodule of `S`. -/
theorem localized₀_range_algebraLinearMap :
    (LinearMap.range (Algebra.linearMap A C)).localized₀ M
        (IsScalarTower.toAlgHom A C S).toLinearMap
      = (LinearMap.range (Algebra.linearMap R S)).restrictScalars A := by
  rw [← LinearMap.range_localizedMap_eq_localized₀_range M (Algebra.linearMap A R)
    (IsScalarTower.toAlgHom A C S).toLinearMap (Algebra.linearMap A C),
    isLocalizedModule_map_algebraLinearMap M]
  rfl

/-- **Localizing the image of the base ring**: the localization at `M` of the image of `A` in `C`
is the image of `R` in `S`.

This is the statement that lets a submodule of `C` built from the image of `A` be compared with
its localizations, hence be computed one maximal ideal at a time. -/
theorem localized'_range_algebraLinearMap :
    (LinearMap.range (Algebra.linearMap A C)).localized' R M
        (IsScalarTower.toAlgHom A C S).toLinearMap
      = LinearMap.range (Algebra.linearMap R S) :=
  restrictScalars_injective A R S <| by
    rw [restrictScalars_localized', localized₀_range_algebraLinearMap (R := R) M]

/-- Localization of submodules preserves binary joins.

Mathlib has `Submodule.localized'_iSup`; this is the `Bool`-indexed case of it. -/
theorem localized'_sup (M' M'' : Submodule A C) :
    (M' ⊔ M'').localized' R M (IsScalarTower.toAlgHom A C S).toLinearMap
      = M'.localized' R M (IsScalarTower.toAlgHom A C S).toLinearMap ⊔
        M''.localized' R M (IsScalarTower.toAlgHom A C S).toLinearMap := by
  simpa [iSup_bool_eq] using
    localized'_iSup R M (IsScalarTower.toAlgHom A C S).toLinearMap
      (fun b : Bool => cond b M' M'')

/-- The image of `A` in `C`, enlarged by `I • C` for an ideal `I` of `A`, localizes to the image
of `R` in `S` enlarged by `(I R) • S`. -/
theorem localized'_sup_smul_top_range_algebraLinearMap (I : Ideal A) :
    (LinearMap.range (Algebra.linearMap A C) ⊔ I • (⊤ : Submodule A C)).localized' R M
        (IsScalarTower.toAlgHom A C S).toLinearMap
      = LinearMap.range (Algebra.linearMap R S) ⊔
        I.map (algebraMap A R) • (⊤ : Submodule R S) := by
  rw [localized'_sup, localized'_range_algebraLinearMap (R := R) M, localized'_smul,
    localized'_top, Ideal.localized'_eq_map]

end Submodule

end
