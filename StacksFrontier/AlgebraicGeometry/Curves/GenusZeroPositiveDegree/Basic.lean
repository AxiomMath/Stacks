module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0C6T: a positive-degree invertible sheaf on a genus-zero curve

Let `k` be a field and let `X` be a proper curve over `k` with `H⁰(X, 𝒪_X) = k` and genus `0`,
and let `ℒ` be an invertible `𝒪_X`-module of degree `d > 0`.
[Stacks, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T) asserts

1. `dim_k H⁰(X, ℒ) = d + 1` and `dim_k H¹(X, ℒ) = 0`, and
2. `ℒ` is very ample and defines a closed immersion of `X` into `𝐏^d_k`.

This file proves the two halves of assertion (1). Assertion (2) is
`AlgebraicGeometry.isRelativelyVeryAmple_and_isClosedImmersion_of_basis`.

The source's route to assertion (1) is the exact sequence of the zero scheme `D` of a nonzero
section `s` of `ℒ`,
`0 ⟶ 𝒪_X ⟶ ℒ ⟶ i_* (ℒ|_D) ⟶ 0` ([Stacks, Tag 01X0] and [Stacks, Tag 0C6K]).
Its outer terms have vanishing `H¹`: on the left because the genus is zero, on the right because
`D` is finite over `k`, hence affine. So `H¹(X, ℒ) = 0`, and then `dim_k H⁰(X, ℒ) = d + 1` is
Riemann-Roch. The nonzero section exists because Riemann-Roch already gives
`dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = d + 1 > 0`.

## Main definitions

* `AlgebraicGeometry.restrictZeroScheme`: the restriction of an invertible module to the zero
  scheme of one of its global sections, pushed forward to the ambient scheme. This is the third
  term of the exact sequence of [Stacks, Tag 0C6K].

## Main results

* `AlgebraicGeometry.exists_eval_top_ne_zero_of_invertibleCurveDegree_pos`: a positive-degree
  invertible module on a proper curve of genus zero with `H⁰(X, 𝒪_X) = k` has a nonzero global
  section.
* `AlgebraicGeometry.isZero_cohomologyOverField_one_of_genus_zero_of_degree_pos`:
  **[Stacks, Tag 0C6T], the vanishing `H¹(X, ℒ) = 0` of assertion (1).**
* `AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_degree_add_one_of_genus_zero`:
  **[Stacks, Tag 0C6T], the dimension count `dim_k H⁰(X, ℒ) = d + 1` of assertion (1).**
* `AlgebraicGeometry.isZero_cohomologyOverField_one_of_genus_eq_zero` and
  `AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_invertibleCurveDegree_add_one`: the same
  two conclusions from a regular global section of `ℒ` whose zero scheme has zero-dimensional
  support.
* `AlgebraicGeometry.finrank_globalSections_eq_invertibleCurveDegree_add_one`: the same count
  for the `k`-vector space of global sections `Γ(ℒ, ⊤)`.
* `AlgebraicGeometry.smul_globalSections_eq`: the `k`-action on `Γ(ℒ, ⊤)` used there is
  multiplication by the image of `k` in `Γ(X, 𝒪_X)`.

## Implementation notes

**Spellings.** The genus is `AlgebraicGeometry.genus` ([Stacks, Tag 0BY7]), the degree is
`AlgebraicGeometry.invertibleCurveDegree` ([Stacks, Tag 0AYR]), `dim_k Hⁱ(X, ℱ)` is
`Module.finrank k (AlgebraicGeometry.cohomologyOverField k f ℱ i)` ([Stacks, Tag 0BEF]) and
`H⁰(X, 𝒪_X) = k` is `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)`. A proper curve is a proper
integral scheme over `k` of dimension at most one; separatedness and finite type are part of
properness, and dimension exactly one is not needed.

The `k`-vector space of global sections is `Γ(ℒ, ⊤)` with the restriction of scalars along the
structure morphism, `AlgebraicGeometry.restrictScalarsOverBase`, through which
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` identifies it with `H⁰(X, ℒ)`.

## References

* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The restriction of an invertible module to the zero scheme of a global section**, pushed
forward to the ambient scheme: for `s` a global section of `ℒ` with zero scheme `i : D ⟶ X`
([Stacks, Tag 02OQ]), this is `i_* i^* ℒ`, written `i_* (ℒ|_D)` in the source. It is the third
term of the exact sequence of [Stacks, Tag 0C6K]. -/
public noncomputable abbrev restrictZeroScheme (X : Scheme.{u}) (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections) :
    X.Modules :=
  (Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj
    ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).obj L)

/-- **The genus-zero hypothesis in the cohomology the degree is computed from.** The genus is
`dim_k H¹(X, 𝒪_X)` for the pushforward presentation of cohomology; this transports the dimension
to `AlgebraicGeometry.cohomologyOverField` along
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`. -/
public theorem finrank_cohomologyOverField_unit_one_eq_zero_of_genus_eq_zero
    (hgenus : genus f = 0) :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) = 0 := by
  rw [← (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
  exact (genus_eq_finrank_structureSheafCohomology f).symm.trans hgenus

/-- **`H¹(X, ℒ) = 0` from a regular section with zero-dimensional zero locus.** Let `X` be proper
over a field `k` with genus zero, let `H¹(X, 𝒪_X)` be finite-dimensional, and let the invertible
module `ℒ` have a regular global section whose zero scheme carries a coherent restriction of `ℒ`
with zero-dimensional support. Then `H¹(X, ℒ) = 0`. The form of
[Stacks, Tag 0C6T] (1) with only the hypotheses of the source is
`AlgebraicGeometry.isZero_cohomologyOverField_one_of_genus_zero_of_degree_pos`. -/
public theorem isZero_cohomologyOverField_one_of_genus_eq_zero [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hgenus : genus f = 0)
    (h02O6 :
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1))
    (hdivisor : ∃ s : L.sections, Mono (L.unitHomEquiv.symm s) ∧
      (restrictZeroScheme X L s).IsCoherent ∧
      topologicalKrullDim (_root_.SheafOfModules.supp (restrictZeroScheme X L s)) ≤ 0) :
    IsZero (cohomologyOverField k f L 1) := by
  obtain ⟨s, hs, hcoh, hsupp⟩ := hdivisor
  have hunit : IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr <| Module.finrank_zero_iff.mp
      (finrank_cohomologyOverField_unit_one_eq_zero_of_genus_eq_zero k f hgenus)
  have hrestrict : IsZero (cohomologyOverField k f (restrictZeroScheme X L s) 1) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f
      (restrictZeroScheme X L s) hsupp 1 Nat.one_pos
  obtain ⟨_, hSE⟩ := shortExact_zeroScheme_of_isRegularSection X L s hs
  exact isZero_cohomologyOverField_of_shortExact k f hSE 1 hunit hrestrict

/-- **`dim_k H⁰(X, ℒ) = d + 1` from a regular section with zero-dimensional zero locus.** Under the
hypotheses of `AlgebraicGeometry.isZero_cohomologyOverField_one_of_genus_eq_zero`, together with
the vanishing of the cohomology of `ℒ` and `𝒪_X` in degrees at least two and
`dim_k H⁰(X, 𝒪_X) = 1`, the degree `(h⁰(ℒ) - h¹(ℒ)) - (h⁰(𝒪_X) - h¹(𝒪_X))` of `ℒ` is
`dim_k H⁰(X, ℒ) - 1`. The form of [Stacks, Tag 0C6T] (1) with only the hypotheses of the source is
`AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_degree_add_one_of_genus_zero`. -/
public theorem finrank_cohomologyOverField_zero_eq_invertibleCurveDegree_add_one [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hgenus : genus f = 0)
    (h02O6 :
      FiniteDimensional k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1))
    (hdivisor : ∃ s : L.sections, Mono (L.unitHomEquiv.symm s) ∧
      (restrictZeroScheme X L s).IsCoherent ∧
      topologicalKrullDim (_root_.SheafOfModules.supp (restrictZeroScheme X L s)) ≤ 0)
    (hvanL : ∀ m, 2 ≤ m → IsZero (cohomologyOverField k f L m))
    (hvanO : ∀ m, 2 ≤ m →
      IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) m))
    (hH0O :
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) =
      @invertibleCurveDegree k _ X f _ hdim L hL + 1 := by
  have hone : Module.finrank k (cohomologyOverField k f L 1) = 0 := by
    have _ := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_one_of_genus_eq_zero k f L hgenus h02O6 hdivisor)
    exact Module.finrank_zero_of_subsingleton
  rw [@invertibleCurveDegree_eq_sub_of_isZero k _ X f _ hdim L hL hvanL hvanO, hone, hH0O,
    finrank_cohomologyOverField_unit_one_eq_zero_of_genus_eq_zero k f hgenus]
  push_cast
  ring

/-- **The `k`-action on the global sections of a module over a scheme over `k`** is
multiplication by the image of `k` in `Γ(X, 𝒪_X)` under the structure morphism. The underlying
type of `(restrictScalarsOverBase k f).obj Γ(ℱ, ⊤)` is `Γ(ℱ, ⊤)` itself. -/
public theorem smul_globalSections_eq (F : X.Modules) (c : k)
    (σ : (restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F)) :
    (show Γ(F, ⊤) from c • σ) =
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c) • (show Γ(F, ⊤) from σ) := by
  have h : f.appLE ⊤ ⊤ (by simp) = f.appTop := Scheme.Hom.appLE_eq_app f
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom c) •
    (show Γ(F, ⊤) from σ) = _
  rw [h]

/-- **A positive-degree invertible module on a genus-zero proper curve has a nonzero global
section.** -/
public theorem exists_eval_top_ne_zero_of_invertibleCurveDegree_pos [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hgenus : genus f = 0) (hpos : 0 < invertibleCurveDegree k f hdim L) :
    ∃ s : L.sections, s.eval (op ⊤) ≠ 0 := by
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  rw [hgenus] at hRR
  have hpos0 : 0 < Module.finrank k (cohomologyOverField k f L 0) := by omega
  have := Module.nontrivial_of_finrank_pos (R := k) hpos0
  obtain ⟨a, ha⟩ := exists_ne (0 : cohomologyOverField k f L 0)
  set y := (cohomologyOverFieldZeroLinearIso k f L).hom a
  have hy : y ≠ 0 := fun h => ha (by
    rw [← (cohomologyOverFieldZeroLinearIso k f L).hom_inv_id_apply a]
    change (cohomologyOverFieldZeroLinearIso k f L).inv y = 0
    rw [h, map_zero])
  refine ⟨(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal L
    Limits.isTerminalTop).symm y, fun h0 => hy ?_⟩
  rw [← (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal L
    Limits.isTerminalTop).apply_symm_apply y]
  exact h0

/-- **[Stacks, Tag 0C6T]: the vanishing `H¹(X, ℒ) = 0` of assertion (1).** Let `X` be a proper
curve over a field `k` with `H⁰(X, 𝒪_X) = k` and genus zero, and let `ℒ` be an invertible
`𝒪_X`-module of positive degree. Then `H¹(X, ℒ) = 0`. -/
@[stacks 0C6T "part (1), the clause `dim_k H¹(X, ℒ) = 0`"]
public theorem isZero_cohomologyOverField_one_of_genus_zero_of_degree_pos [IsProper f]
    [IsIntegral X] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hgenus : genus f = 0) (hpos : 0 < invertibleCurveDegree k f hdim L) :
    IsZero (cohomologyOverField k f L 1) := by
  obtain ⟨s, hs⟩ := exists_eval_top_ne_zero_of_invertibleCurveDegree_pos k f hdim L hgenus hpos
  have hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := ‹_›
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    isRegularSection_of_eval_top_ne_zero L s hs
  set D := zeroScheme X L (s.eval (op ⊤))
  have hfin : IsFinite (D.subschemeι ≫ f) :=
    isFinite_zeroScheme_of_eval_top_ne_zero k f hdim L s hs
  have hnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hnoethZ : IsLocallyNoetherian D.subscheme :=
    isLocallyNoetherian_of_isFinite (D.subschemeι ≫ f)
  have hLstacks : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hLcoh : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have hpull : SheafOfModules.IsCoherent ((Scheme.Modules.pullback D.subschemeι).obj L) :=
    isCoherent_pullback D.subschemeι L
  have hqc : ((Scheme.Modules.pullback D.subschemeι).obj L).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have hD : IsAffine D.subscheme := isAffine_of_isAffineHom (D.subschemeι ≫ f)
  have hrestrict : IsZero (cohomologyOverField k f (restrictZeroScheme X L s) 1) :=
    (isZero_cohomologyOverField_pos_of_isAffine k (D.subschemeι ≫ f) _ 1 Nat.one_pos).of_iso
      (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k D.subschemeι f _ 1).symm
  obtain ⟨_, hSE⟩ := shortExact_zeroScheme_of_isRegularSection X L s hreg
  exact isZero_cohomologyOverField_of_shortExact k f hSE 1
    (isZero_cohomologyOverField_unit_one_of_genus_eq_zero k f hgenus) hrestrict

/-- **[Stacks, Tag 0C6T]: the dimension count `dim_k H⁰(X, ℒ) = d + 1` of assertion (1).** On a
proper curve over a field with `H⁰(X, 𝒪_X) = k` and genus zero, an invertible module `ℒ` whose
degree `d` is positive has `dim_k H⁰(X, ℒ) = d + 1`. -/
@[stacks 0C6T "part (1), the clause `dim_k H⁰(X, ℒ) = d + 1`"]
public theorem finrank_cohomologyOverField_zero_eq_degree_add_one_of_genus_zero
    [IsProper f] [IsIntegral X] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hgenus : genus f = 0) (hpos : 0 < invertibleCurveDegree k f hdim L) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ) =
      invertibleCurveDegree k f hdim L + 1 := by
  have hone : Module.finrank k (cohomologyOverField k f L 1) = 0 := by
    have _ := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_one_of_genus_zero_of_degree_pos k f hdim L hgenus hpos)
    exact Module.finrank_zero_of_subsingleton
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  rw [hone, hgenus] at hRR
  push_cast at hRR
  linarith

/-- **The dimension count of [Stacks, Tag 0C6T] for the global sections themselves.** Under the
hypotheses of `AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_degree_add_one_of_genus_zero`
the `k`-vector space `Γ(ℒ, ⊤)`, with `k` acting through the structure morphism, has dimension
`d + 1`. It is identified with `H⁰(X, ℒ)` by `AlgebraicGeometry.cohomologyOverFieldZeroLinearIso`.
-/
public theorem finrank_globalSections_eq_invertibleCurveDegree_add_one [IsProper f]
    [IsIntegral X] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hgenus : genus f = 0) (hpos : 0 < invertibleCurveDegree k f hdim L) :
    (Module.finrank k ((restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)) : ℤ) =
      invertibleCurveDegree k f hdim L + 1 := by
  rw [← (cohomologyOverFieldZeroLinearIso k f L).toLinearEquiv.finrank_eq]
  exact finrank_cohomologyOverField_zero_eq_degree_add_one_of_genus_zero k f hdim L hgenus hpos

end AlgebraicGeometry

end
