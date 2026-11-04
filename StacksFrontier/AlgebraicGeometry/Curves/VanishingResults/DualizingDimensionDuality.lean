module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDualityLinear
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
import StacksCore.Tactic.StacksAttribute

/-!
# The duality of dimensions on a proper curve, at the structure sheaf

Let `k` be a field and `X` a proper `k`-scheme of dimension at most one, and let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of [Stacks, Tag 0BS2]. Clause (5) of
that tag, `Hom_{𝒪_X}(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)`, is formalized as
`Stacks.Duality.clauseFiveAddEquiv`, but only as an isomorphism of abelian groups, which does
not compare dimensions over `k`. This file upgrades it to a `k`-linear isomorphism and reads off
the resulting equality of dimensions

`dim_k Hom_{𝒪_X}(ℱ, ω_X) = dim_k H¹(X, ℱ)`

for a coherent quasi-coherent `ℱ`. At `ℱ = 𝒪_X` the left-hand side is `dim_k H⁰(X, ω_X)`, and the
equality is the case `i = 1`, `ℰ = 𝒪_X` of the duality of dimensions of
[Stacks, Tag 0BS6], clause (3).

## Main results

The elided prefix is `AlgebraicGeometry`.

* `cohomologyOverFieldMap_smul_id`: `Hⁿ(X, a • 𝟙) = a • 𝟙`.
* `Stacks.Duality.clauseFiveLinearEquiv`: **clause (5) of [Stacks, Tag 0BS2] as an isomorphism
  of `k`-vector spaces.**
* `unitHomLinearEquivGlobalSections`: `Hom_{𝒪_X}(𝒪_X, ℳ) ≃ₗ[k] Γ(X, ℳ)`.
* `finrank_hom_dualizingSheafOverField_eq_finrank_cohomologyOverField_one`:
  `dim_k Hom_{𝒪_X}(ℱ, ω_X) = dim_k H¹(X, ℱ)`.
* `finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_finrank_one_unit`:
  **`dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`**, the case `i = 1`, `ℰ = 𝒪_X` of the duality of
  dimensions of [Stacks, Tag 0BS6], clause (3).

## What [Stacks, Tag 0BS6] asserts, and what of it is proved here

Tag 0BS6 is about a proper scheme `X` over a field `k` which is Gorenstein and equidimensional
of dimension one, with `ω_X` the dualizing sheaf of [Stacks, Tag 0BS2]. It asserts: (1) `ω_X` is
invertible; (2) `deg(ω_X) = -2χ(X, 𝒪_X)`; (3) for a finite locally free `ℰ` of constant rank,
`χ(X, ℰ) = deg(ℰ) - ½ rank(ℰ) deg(ω_X)`, and `dim_k Hⁱ(X, ℰ) = dim_k H^{1-i}(X, ℰ^∨ ⊗ ω_X)` for
every integer `i`.

What is proved here is the single equality `dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`, which is the
last assertion at `i = 1` and `ℰ = 𝒪_X`, where the twist `ℰ^∨ ⊗ ω_X` is `ω_X` itself. It is
proved for an arbitrary proper `X` of dimension at most one: neither Gorensteinness nor
equidimensionality is used, so the statement below is more general than the tag in its
hypotheses.

The same `i = 1` assertion at an arbitrary finite locally free `ℰ` of constant rank — where the
twist `ℰ^∨ ⊗ ω_X` is a genuinely different sheaf — is
`AlgebraicGeometry.finrank_cohomologyOverField_zero_dualTensorDualizingSheafOverField_eq_one`
in `Curves/VanishingResults/DualizingDimensionDualityBundle.lean`, which is the statement below
composed with the `k`-linear form of [Stacks, Tag 0882] at `U = ⊤` and with the identification
`𝓗om(ℰ, ω_X) = ℰ^∨ ⊗ ω_X`. The latter is step (5) of the proof of [Stacks, Tag 08JJ] read at a
finite locally free module,
`Stacks.SheafOfModules.isIso_tensorDualToSheafHom_of_isFiniteLocallyFreeOfRank`; it is obtained
from the *sectionwise* local hypothesis of
`Stacks.SheafOfModules.isIso_tensorDualToSheafHom` rather than from the per-object summand
condition of [Stacks, Tag 0FNY], for which no bridge out of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` exists.

Clause (2) and the Riemann--Roch formula of clause (3) are proved in
`Curves/VanishingResults/DualizingCanonicalDegree.lean`, and the duality of dimensions at `i = 0`
in `Curves/VanishingResults/DualizingDimensionDualityZero.lean`; each of those three carries
clause (1) of the tag, that `ω_X` is invertible, as a hypothesis, and clause (1) is proved
nowhere. They do *not* rest on [Stacks, Tag 0BS3] beyond clause (1): clause (2) is
[Stacks, Tag 0BS5] together with the definition of the degree of [Stacks, Tag 0AYR], the
Riemann--Roch formula is clause (2) together with that same definition, and the `i = 0` duality
is the `i = 1` duality at the twist `ℰ^∨ ⊗ ω_X`. In particular no Chow theory, and neither
equation [Stacks, Tag 0BRY] nor [Stacks, Tag 0BRZ], is used for the Riemann--Roch formula.

Clause (1) itself rests on the dualizing character of the canonical complex
`ω_X^• = f^×(𝒪_{Spec k})`, together with `ω_X^• = ω_X[1]` for a Cohen--Macaulay equidimensional
curve ([Stacks, Tag 0BS3]) and the *geometric* form of clause (1)(a) of [Stacks, Tag 0BFQ] —
that every point has an affine open `V` with `ω_X^•|_V ≅ 𝒪_V[n]`. **Neither of those two is
available either.** Of clause (1)(a) what is formalized is
`Stacks.Duality.isGorenstein_iff_hasInvertibleDualizingModelOn`, which reads the condition at the
affine-local models only; the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/InvertibleDualizing.lean` record that
passing to the geometric form needs the derived comparison `(ω^~)|_{D(f)} ≅ (ω_f)^~`, absent from
this tree, and its ring-level form
`Dualizing.isGorensteinRing_iff_isInvertible_canonical` is what is formalized instead. Reading
`ω_X^•` as an invertible object of `D(𝒪_X)` and taking its cohomology sheaf is no way round it:
that needs the direction (1) ⟹ (2) of [Stacks, Tag 0FPG], of which
`StacksFrontier/Topology/Sheaves/Cohomology/InvertibleDerivedObjects.lean` has only clause (2) and
the perfectness it implies. So clause (1) would not follow from the dualizing character alone.
That dualizing character is
`Stacks.Duality.IsDualizingComplex (Stacks.Duality.dualizingComplexOverField f)`, which has no
proof in this development. The input it lacks is the affine-chart description of the twisted
inverse image — [Stacks, Tag 0AA1] together with clause (b) of [Stacks, Tag 0BV2] — which is what
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts` ([Stacks, Tag 0AA3]) takes as its
hypothesis `h0AA1` and what the `stacks 0BV2` note of
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekAffineComparison/OpenSquare.lean` declines;
without it `(f^×(𝒪_{Spec k}))|_U` is not computed at any affine open. ([Stacks, Tag 0AWP], [Stacks, Tag 0BRT], [Stacks, Tag 0AWT] and [Stacks, Tag 0E9H] are not
the missing input: they are a representability statement for the dualizing *module*, the smooth
proper case of `a(𝒪_S) = ∧^dΩ[d]`, a tag which is in fact formalized in its clause (3), and an
exercise about sheaves on a topological space.) The nearest thing the development does have is
`Stacks.Duality.isDualizingComplex_unit_overField`, which proves
`Stacks.Duality.IsDualizingComplex` of the *structure sheaf* of a Gorenstein scheme locally of
finite type over a field; that is a different complex from `ω_X^•`.

## What of [Stacks, Tag 0BS3] is proved here

Clause (4) of that tag is the family of isomorphisms
`Ext^{1+i}_X(ℱ, ω_X) = Hom_k(H^{-i}(X, ℱ), k)` for quasi-coherent `ℱ`. Its member at `i = -1` has
`Ext⁰` on the left, which is the Hom-group itself, and is therefore exactly
`Stacks.Duality.clauseFiveLinearEquiv` — the `k`-linear form of clause (5) of
[Stacks, Tag 0BS2]. That member carries the tag's attribute below; no other degree is proved, and
neither is clause (1), clause (3) or the coherence half of clause (2), all of which need
`ω_X^• = ω_X[1]`.

## Implementation notes

*The `k`-linear structure.* `CategoryTheory.Linear k X.Modules` cannot be an instance — the base
ring is not determined by the scheme — so the intermediate statements take it and
`CategoryTheory.Functor.Linear k (AlgebraicGeometry.globalSectionsOver f)` as instance
arguments, exactly as `StacksFrontier/AlgebraicGeometry/Duality/ProperOverFieldDualityLinear.lean`
does. The final equality of dimensions mentions neither, and discharges both with
`AlgebraicGeometry.Scheme.Modules.linearOverBase` and
`AlgebraicGeometry.globalSectionsOver_linear_linearOverBase`.

*How the scalar is moved across clause (5).* Clause (5) is natural in `ℱ`
(`Stacks.Duality.clauseFiveAddEquiv_naturality`) and `a • φ = (a • 𝟙) ≫ φ` in a `k`-linear
category, so naturality at `a • 𝟙` turns the scalar on the left into `H¹(X, a • 𝟙)` on the
right, which is `a • 𝟙` by `AlgebraicGeometry.cohomologyOverFieldMap_smul_id`. That lemma in
turn reads `AlgebraicGeometry.cohomologyOverFieldMap` through the comparison with
hypercohomology and uses `k`-linearity of `DerivedCategory.singleFunctor` and of
`RΓ(X, -) ⋙ Hⁿ`. This is the same argument as `Stacks.Duality.dualityAddEquivZero_smul`.

*Two spellings of the global sections functor.*
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` lands in
`AlgebraicGeometry.restrictScalarsOverBase` applied to evaluation at `⊤`, while
`AlgebraicGeometry.globalSectionsOver` restricts scalars along `f.appTop`; the two functors are
equal by `AlgebraicGeometry.sectionsOverBase_eq_globalSectionsOver` but not definitionally, and
that equality is what `cohomologyOverFieldZeroLinearEquivGlobalSectionsOver` transports along.

*Finite dimensionality.* A space and its `k`-linear dual have the same dimension only in finite
dimensions; `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper` supplies it
for a coherent module on a proper scheme over a field.

## References

* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BS4](https://stacks.math.columbia.edu/tag/0BS4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

section Linearity

variable [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- **`Hⁿ(X, a • 𝟙) = a • 𝟙`.** Sheaf cohomology over the base field is the degree-`n`
hypercohomology of the module placed in degree zero, and both the inclusion in degree zero and
`RΓ(X, -) ⋙ Hⁿ` are `k`-linear, so the composite sends `a • 𝟙` to `a • 𝟙`. -/
public theorem cohomologyOverFieldMap_smul_id (F : X.Modules) (n : ℕ) (a : k) :
    cohomologyOverFieldMap k f (a • 𝟙 F) n = a • 𝟙 (cohomologyOverField k f F n) := by
  have hnat :=
    Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap
      k f n (a • 𝟙 F)
  have hmap : (DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} k) (n : ℤ)).map (a • 𝟙 F) =
      a • 𝟙 (Stacks.Duality.derivedCohomologyOverField f
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) (n : ℤ)) := by
    rw [Functor.comp_map, Functor.comp_map, (DerivedCategory.singleFunctor X.Modules 0).map_smul,
      (DerivedCategory.singleFunctor X.Modules 0).map_id]
    exact Stacks.Duality.derivedCohomologyOverField_map_smul_id f _ _ a
  rw [hmap] at hnat
  rw [Linear.comp_smul, Category.comp_id] at hnat
  have := hnat.trans (by rw [Linear.smul_comp, Category.id_comp] :
    a • (Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).hom =
      (a • 𝟙 (cohomologyOverField k f F n)) ≫
        (Stacks.Duality.cohomologyOverFieldIsoDerivedCohomologyOverField k f F n).hom)
  exact (cancel_mono _).mp this

end Linearity

end AlgebraicGeometry

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- **Clause (5) of [Stacks, Tag 0BS2] commutes with the action of `k`.** Writing `a • φ` as
`(a • 𝟙) ≫ φ` and applying `Stacks.Duality.clauseFiveAddEquiv_naturality` turns the scalar into
`H¹(X, a • 𝟙)`, which is `a • 𝟙` by
`AlgebraicGeometry.cohomologyOverFieldMap_smul_id`. -/
public theorem clauseFiveAddEquiv_smul (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) (a : k) (φ : F ⟶ dualizingSheafOverField f) :
    clauseFiveAddEquiv f hdim F hF (a • φ) = a • clauseFiveAddEquiv f hdim F hF φ := by
  have h : a • φ = (a • 𝟙 F) ≫ φ := by rw [Linear.smul_comp, Category.id_comp]
  rw [h, clauseFiveAddEquiv_naturality f hdim F F hF hF (a • 𝟙 F) φ,
    AlgebraicGeometry.cohomologyOverFieldMap_smul_id f F 1 a]
  ext x
  simp

/-- **Clause (5) of [Stacks, Tag 0BS2] as an isomorphism of `k`-vector spaces:**

  `Hom_{𝒪_X}(ℱ, ω_X) ≃ₗ[k] Hom_k(H¹(X, ℱ), k)`

for a quasi-coherent `ℱ` on a proper `X` of dimension at most one over `k`. The `k`-structure on
the left is the one `X.Modules` carries over the base, and the `k`-linearity is what makes the
identification count dimensions over `k`.

Read with `Ext⁰` for `Hom`, this is also the degree `i = -1` member of the family of clause (4) of
[Stacks, Tag 0BS3].

[Stacks, Tag 0BS3] (not registered here: this is not the whole statement of the tag): clause (4)
at the single degree i = -1, where the tag's Ext^(1+i) is Ext^0 and so is the Hom-group itself:
Hom(F, omega_X) = Hom_k(H^1(X, F), k) for quasi-coherent F, as an isomorphism of k-vector spaces,
which is what the tag's Hom_k asserts. It holds for a proper scheme of dimension at most one over
a field, so without the Cohen-Macaulay and equidimensionality hypotheses of the tag. No other
degree of clause (4) is proved, and neither is clause (1), clause (3), nor the coherence half of
clause (2): those need the identification omega^bullet = omega_X[1] and the dualizing character of
f^x(O_Spec k), which this development does not have. The Cohen-Macaulay half of clause (2) is
Stacks.Duality.isZero_of_mono_dualizingSheafOverField_of_supp_dim_le_zero and the nonemptiness of
the support is AlgebraicGeometry.CohenMacaulayCurveSituation.not_isZero_dualizingSheafOverField,
both in Curves/VanishingResults/DualizingSheafCohenMacaulay.lean
-/
public def clauseFiveLinearEquiv (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ dualizingSheafOverField f) ≃ₗ[k] (cohomologyOverField k f F 1 →ₗ[k] k) where
  __ := clauseFiveAddEquiv f hdim F hF
  map_smul' := clauseFiveAddEquiv_smul f hdim F hF

end Stacks.Duality

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [Linear k X.Modules] [Functor.Linear k (globalSectionsOver f)]

/-- **A morphism out of `𝒪_X` is its value on the section `1`.** The opens of a scheme have a
terminal object, so a compatible family of sections is a section over `⊤`. -/
public def unitHomEquivSectionsTop (M : X.Modules) :
    (Stacks.Ample.unitModule X ⟶ M) ≃ Γ(M, ⊤) :=
  (SheafOfModules.unitHomEquiv M).trans
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M
      (Limits.isTerminalTop (α := X.Opens)))

/-- **`Hom_{𝒪_X}(𝒪_X, ℳ) ≃ₗ[k] Γ(X, ℳ)`.** The bijection is
`AlgebraicGeometry.unitHomEquivSectionsTop`, and it is `k`-linear because `k`-linear global
sections is a `k`-linear functor: evaluating its action on `a • φ` at the section `1` of `𝒪_X`
is the required equality. -/
public def unitHomLinearEquivGlobalSections (M : X.Modules) :
    (Stacks.Ample.unitModule X ⟶ M) ≃ₗ[k] (globalSectionsOver f).obj M where
  __ := unitHomEquivSectionsTop M
  map_add' φ ψ := rfl
  map_smul' a φ := by
    have h : (globalSectionsOver f).map (a • φ) = a • (globalSectionsOver f).map φ :=
      Functor.map_smul (globalSectionsOver f) a φ
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom h) _

/-- **`H⁰(X, ℳ) ≃ₗ[k] Γ(X, ℳ)`**, with the target read at the spelling
`AlgebraicGeometry.globalSectionsOver` uses. This is
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` followed by the equality of functors
`AlgebraicGeometry.sectionsOverBase_eq_globalSectionsOver`, which reconciles the two spellings
`f.appLE ⊤ ⊤` and `f.appTop` of the structure map. -/
public def cohomologyOverFieldZeroLinearEquivGlobalSectionsOver (M : X.Modules) :
    cohomologyOverField k f M 0 ≃ₗ[k] (globalSectionsOver f).obj M :=
  (cohomologyOverFieldZeroLinearIso k f M).toLinearEquiv.trans
    (eqToIso (congrArg (fun G : X.Modules ⥤ ModuleCat.{u} k => G.obj M)
      (sectionsOverBase_eq_globalSectionsOver f))).toLinearEquiv

/-- **`dim_k H⁰(X, ℳ) = dim_k Hom_{𝒪_X}(𝒪_X, ℳ)`.** -/
public theorem finrank_cohomologyOverField_zero_eq_finrank_hom_unit (M : X.Modules) :
    Module.finrank k (cohomologyOverField k f M 0) =
      Module.finrank k (Stacks.Ample.unitModule X ⟶ M) :=
  ((cohomologyOverFieldZeroLinearEquivGlobalSectionsOver f M).trans
    (unitHomLinearEquivGlobalSections f M).symm).finrank_eq

/-- **`dim_k Hom_{𝒪_X}(ℱ, ω_X) = dim_k H¹(X, ℱ)`** for a coherent quasi-coherent `ℱ` on a proper
scheme of dimension at most one over a field: clause (5) of [Stacks, Tag 0BS2], read `k`-linearly
and with the `k`-linear dual of a finite-dimensional space having the dimension of that
space. -/
public theorem finrank_hom_dualizingSheafOverField_eq_finrank_cohomologyOverField_one
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsQuasicoherent) [F.IsCoherent] :
    Module.finrank k (F ⟶ Stacks.Duality.dualizingSheafOverField f) =
      Module.finrank k (cohomologyOverField k f F 1) := by
  have : FiniteDimensional k (cohomologyOverField k f F 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f F 1
  rw [(Stacks.Duality.clauseFiveLinearEquiv f hdim F hF).finrank_eq]
  exact Subspace.dual_finrank_eq

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **`dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`** for a proper scheme `X` of dimension at most one
over a field `k`, with `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` the dualizing sheaf of
[Stacks, Tag 0BS2].

This is the duality of dimensions of [Stacks, Tag 0BS6], clause (3), at `i = 1` and at the
vector bundle `ℰ = 𝒪_X`, for which the twist `ℰ^∨ ⊗ ω_X` is `ω_X` itself. The proof is clause
(5) of [Stacks, Tag 0BS2] at `ℱ = 𝒪_X`, read `k`-linearly: `Hom_{𝒪_X}(𝒪_X, ω_X)` is
`H⁰(X, ω_X)` on the one side and the `k`-linear dual of `H¹(X, 𝒪_X)` on the other. Neither the
Gorenstein nor the equidimensionality hypothesis of the tag is used.

[Stacks, Tag 0BS6] (not registered here: this is not the whole statement of the tag): the duality
of dimensions of clause (3) at i = 1 and at the vector bundle E = O_X, for which the twist E^dual
tensor omega_X is omega_X itself: dim_k H^0(X, omega_X) = dim_k H^1(X, O_X), proved from clause
(5) of Tag 0BS2 read k-linearly, for a proper scheme of dimension at most one over a field and so
without the Gorenstein and equidimensionality hypotheses of the tag. The same duality at i = 1 and
an arbitrary finite locally free E of constant rank is proved in
Curves/VanishingResults/DualizingDimensionDualityBundle.lean. Of the rest of the tag, clause (2)
and the Riemann-Roch formula of clause (3) are proved in
Curves/VanishingResults/DualizingCanonicalDegree.lean and the duality of dimensions at i = 0 in
Curves/VanishingResults/DualizingDimensionDualityZero.lean. None of those three bears an attribute
of this tag, because each one takes clause (1) of this tag, that omega_X is invertible, among its
binders without proving it, so each proves strictly less than the tag says. Clause (1) is proved
nowhere: it rests on the dualizing character of f^x(O_Spec k), whose one remaining input is Tag
0AA1 together with the main claim of Tag 0BV2
-/
public theorem finrank_cohomologyOverField_zero_dualizingSheafOverField_eq_finrank_one_unit
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) =
      Module.finrank k (cohomologyOverField k f (Stacks.Ample.unitModule X) 1) := by
  let := Scheme.Modules.linearOverBase f
  let : Functor.Linear k (globalSectionsOver f) := globalSectionsOver_linear_linearOverBase f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : (Stacks.Ample.unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  rw [finrank_cohomologyOverField_zero_eq_finrank_hom_unit f,
    finrank_hom_dualizingSheafOverField_eq_finrank_cohomologyOverField_one f hdim
      (Stacks.Ample.unitModule X)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)]

end AlgebraicGeometry

end
