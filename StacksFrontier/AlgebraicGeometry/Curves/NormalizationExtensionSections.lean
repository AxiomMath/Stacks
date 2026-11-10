module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeAffineLocalizations
public import StacksFrontier.AlgebraicGeometry.Curves.SheafDerivationDescent
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.AffineFractionRing
public import StacksFrontier.RingTheory.Derivation.IntegralClosureLocal

/-!
# Extending a vector field to the normalization over an affine open

Let `k` be an algebraically closed field and `X` a reduced one-dimensional `k`-scheme, locally of
finite type, whose singularities are at worst nodal, and let `ν : X^ν ⟶ X` be its normalization.
This file extends a vector field `D` on `X` to the sections of the normalization over the preimage
of an affine open `U`: there is an additive map `E` of `Γ(X^ν, ν⁻¹U)` obeying the Leibniz rule
with `E (ν^♯ r) = ν^♯ (D r)` for every `r : Γ(X, U)`.

The extension is produced in three moves, none of which is about curves.

First, the vector field is read as a `k`-derivation of `Γ(X, U)`. A vector field assigns to each
open an additive map obeying the Leibniz rule and annihilating the sections pulled back from the
base, and the `k`-algebra structure of `Γ(X, U)` relevant here is exactly the pullback of scalars
along the structure morphism, `Stacks.AlgebraicGeometry.UnitsNormalProper.structMapLE`. The
`k`-linearity is then the vanishing on the structural image of a scalar: that image is a
restriction of a section pulled back from `Spec k`, so the Leibniz rule and the restriction
compatibility reduce it to the vanishing on `Spec k` itself.

Second, the derivation is extended to the integral closure of `Γ(X, U)` in its total ring of
fractions. This is a local problem by
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_forall_maximal`, and the local
hypothesis at each maximal ideal is exactly
`Stacks.Curves.exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities`: the
maximal ideal names a point of `U`, the local ring there is regular or nodal, and in both cases
the extension is already known. The finiteness of the set of minimal primes, which the
local-to-global step needs, comes from `Γ(X, U)` being a finite-type `k`-algebra and so
Noetherian.

Third, the ring-theoretic conclusion is transported to sections. Over an affine open the
normalization *is* that integral closure, by
`AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosureFractionRing`, and the
identification is one of `Γ(X, U)`-algebras for the algebra structure given by `ν^♯` itself; so
conjugating the extended derivation by it gives a Leibniz map of `Γ(X^ν, ν⁻¹U)` whose
compatibility with `ν^♯` is the statement that an algebra equivalence commutes with `algebraMap`.

The conclusion is stated for a bare additive map rather than a bundled derivation because that is
the shape in which the germwise comparison
`Stacks.Curves.germ_eq_of_extension_of_extension` consumes it: gluing the extensions built open
by open never uses linearity over anything, only additivity and the Leibniz rule.

## Main results

* `Stacks.Curves.SheafDerivationOf.onSections_structMapLE` — a vector field annihilates the
  structural image of a scalar of the base field.
* `Stacks.Curves.SheafDerivationOf.sectionsDerivation` — the `k`-derivation of `Γ(X, U)` that a
  vector field induces.
* `Stacks.Curves.exists_leibniz_extension_of_extend_integralClosure` — the transport of a
  ring-theoretic extension to the sections of the normalization.
* `Stacks.Curves.exists_leibniz_extension_normalizationSections` — **over an affine open of an
  at-worst-nodal curve a vector field extends to the normalization.**

## References

* [Stacks Project, Tag 0E68](https://stacks.math.columbia.edu/tag/0E68)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 0E66](https://stacks.math.columbia.edu/tag/0E66)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.UnitsNormalProper
open scoped AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace SheafDerivationOf

/-- **A vector field annihilates the structural image of a scalar.** The structural ring map
`k →+* Γ(X, U)` of `Stacks.AlgebraicGeometry.UnitsNormalProper.structMapLE` is the global
sections map of the structure morphism followed by the restriction to `U`; a vector field kills
the first by `Stacks.Curves.SheafDerivationOf.onSections_app` and commutes with the second by
`Stacks.Curves.SheafDerivationOf.onSections_restrict`. -/
public theorem onSections_structMapLE {f : X ⟶ Spec (.of k)} (D : SheafDerivationOf f)
    (U : X.Opens) (c : k) : D.onSections (structMapLE f U c) = 0 := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  have hfac : structMapLE f U c
      = (X.presheaf.map (homOfLE hle).op).hom
        ((f.app ⊤).hom ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := rfl
  rw [hfac, D.onSections_restrict hle, D.onSections_app, map_zero]

/-- **The `k`-derivation of `Γ(X, U)` induced by a vector field.** Its underlying function is
`Stacks.Curves.SheafDerivationOf.onSections`; additivity and the Leibniz rule are axioms of a
vector field, and the `k`-linearity is the vanishing on the structural image of a scalar, the
`k`-algebra structure being required to be the structural one. -/
public def sectionsDerivation {f : X ⟶ Spec (.of k)} (D : SheafDerivationOf f) (U : X.Opens)
    [Algebra k Γ(X, U)] (halg : ∀ c : k, algebraMap k Γ(X, U) c = structMapLE f U c) :
    Derivation k Γ(X, U) Γ(X, U) where
  toFun := D.onSections
  map_add' := D.onSections_add
  map_smul' c r := by
    change D.onSections (c • r) = c • D.onSections r
    have hc : (c • r : Γ(X, U)) = structMapLE f U c * r := by
      rw [Algebra.smul_def, halg]
    rw [hc, D.onSections_mul, D.onSections_structMapLE U c, mul_zero, add_zero,
      Algebra.smul_def, halg]
  map_one_eq_zero' := D.onSections_one
  leibniz' a b := by
    change D.onSections (a * b) = a • D.onSections b + b • D.onSections a
    simpa only [smul_eq_mul] using D.onSections_mul a b

/-- `sectionsDerivation` computes the value of the vector field on a local section. -/
@[simp] public theorem sectionsDerivation_apply {f : X ⟶ Spec (.of k)} (D : SheafDerivationOf f)
    (U : X.Opens) [Algebra k Γ(X, U)]
    (halg : ∀ c : k, algebraMap k Γ(X, U) c = structMapLE f U c) (r : Γ(X, U)) :
    D.sectionsDerivation U halg r = D.onSections r := rfl

end SheafDerivationOf

section Transport

variable [IsReduced X]

/-- **Transporting a ring-theoretic extension to the sections of the normalization.** Over an
affine open `U` of a reduced scheme the sections of the normalization are the integral closure of
`Γ(X, U)` in its total ring of fractions, as `Γ(X, U)`-algebras for the structure given by `ν^♯`
(`AlgebraicGeometry.normalizationSectionsAlgEquivIntegralClosureFractionRing`). Conjugating any
additive, Leibniz extension of a map `d : Γ(X, U) → Γ(X, U)` to that integral closure by the
identification therefore produces an additive, Leibniz map of `Γ(X^ν, ν⁻¹U)` extending `d` along
`ν^♯`. -/
public theorem exists_leibniz_extension_of_extend_integralClosure
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) (d : Γ(X, U) → Γ(X, U))
    (D' : ↥(integralClosure Γ(X, U) (FractionRing Γ(X, U))) →
      ↥(integralClosure Γ(X, U) (FractionRing Γ(X, U))))
    (hadd : ∀ y z, D' (y + z) = D' y + D' z)
    (hmul : ∀ y z, D' (y * z) = y * D' z + z * D' y)
    (hext : ∀ r : Γ(X, U), D' (algebraMap Γ(X, U) _ r) = algebraMap Γ(X, U) _ (d r)) :
    ∃ E : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) →+
          Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U),
      (∀ z w, E (z * w) = z * E w + w * E z) ∧
      (∀ r : Γ(X, U),
        E (((Scheme.normalization X hfin).app U).hom r)
          = ((Scheme.normalization X hfin).app U).hom (d r)) := by
  let algN : Algebra Γ(X, U)
      Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) :=
    ((Scheme.normalization X hfin).app U).hom.toAlgebra
  have e : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) (FractionRing Γ(X, U)) :=
    normalizationSectionsAlgEquivIntegralClosureFractionRing hfin U hU
  refine ⟨AddMonoidHom.mk' (fun z => e.symm (D' (e z))) (fun z w => ?_), fun z w => ?_,
    fun r => ?_⟩
  · rw [map_add, hadd, map_add]
  · change e.symm (D' (e (z * w))) = z * e.symm (D' (e w)) + w * e.symm (D' (e z))
    rw [map_mul, hmul, map_add, map_mul, map_mul, e.symm_apply_apply, e.symm_apply_apply]
  · change e.symm (D' (e (((Scheme.normalization X hfin).app U).hom r)))
      = ((Scheme.normalization X hfin).app U).hom (d r)
    have hr : ((Scheme.normalization X hfin).app U).hom r
        = algebraMap Γ(X, U)
            Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) r := rfl
    rw [hr, e.commutes, hext r, AlgEquiv.commutes]
    rfl

end Transport

/-- **Over an affine open of an at-worst-nodal curve a vector field extends to the
normalization.** Let `k` be algebraically closed and `X` a reduced one-dimensional `k`-scheme,
locally of finite type, whose singularities are at worst nodal, and suppose the quasi-compact
opens of `X` have finitely many irreducible components, so that the normalization
`ν : X^ν ⟶ X` exists. Then a vector field `D` on `X` extends, over the preimage of any affine
open `U`, to an additive map of `Γ(X^ν, ν⁻¹U)` obeying the Leibniz rule and satisfying
`E (ν^♯ r) = ν^♯ (D r)`.

The three steps are: reading `D` as a `k`-derivation of `Γ(X, U)` for the structural `k`-algebra
structure (`Stacks.Curves.SheafDerivationOf.sectionsDerivation`), extending it to the integral
closure of `Γ(X, U)` in its total ring of fractions by the local-to-global principle
`Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_forall_maximal` whose local
input is
`Stacks.Curves.exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities`, and
transporting the result along the identification of that closure with the sections of the
normalization. -/
public theorem exists_leibniz_extension_normalizationSections
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [IsReduced X]
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hfin : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    (D : SheafDerivationOf (X ↘ Spec (.of k)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ E : Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U) →+
          Γ(Scheme.normalizationScheme X hfin, Scheme.normalization X hfin ⁻¹ᵁ U),
      (∀ z w, E (z * w) = z * E w + w * E z) ∧
      (∀ r : Γ(X, U),
        E (((Scheme.normalization X hfin).app U).hom r)
          = ((Scheme.normalization X hfin).app U).hom (D.onSections r)) := by
  let algk : Algebra k Γ(X, U) := (structMapLE (X ↘ Spec (.of k)) U).toAlgebra
  have : _root_.IsReduced Γ(X, U) := AlgebraicGeometry.IsReduced.component_reduced U
  have : Algebra.FiniteType k Γ(X, U) :=
    finiteType_structMapLE (X ↘ Spec (.of k)) ⟨U, hU⟩
  have : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  obtain ⟨D', hD', -⟩ :=
    Stacks.DerivationExtension.existsUnique_extend_integralClosure_of_forall_maximal k Γ(X, U)
      (minimalPrimes.finite_of_isNoetherianRing Γ(X, U))
      (fun P hP D₀ => by
        have := hP
        exact exists_extend_integralClosure_localization_of_hasAtWorstNodalSingularities k X
          hdim hnodal hU P (fun _ => rfl) D₀)
      (D.sectionsDerivation U fun _ => rfl)
  exact exists_leibniz_extension_of_extend_integralClosure hfin hU D.onSections D'
    (fun y z => map_add _ y z) (fun y z => by simpa only [smul_eq_mul] using D'.leibniz y z) hD'

end Stacks.Curves

end
