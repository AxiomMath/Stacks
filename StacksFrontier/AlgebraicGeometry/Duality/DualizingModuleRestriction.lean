module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleMaximalDimension
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing module and restriction to an open subscheme

The first warning of [Stacks, Section 48.22] (the section tag [Stacks, Tag 0AWH]) is that "the
integer `n` may change when passing from `X` to an open `U` of `X` and then it won't be true that
`ω_X|_U = ω_U`", and the section closes the discussion with "the first problem will not occur if
`X` is equidimensional, more precisely, if the dimension function associated to `ω_X^•` maps
every generic point of `X` to the same integer". Both are proved here.

## Main results

* `Stacks.Duality.IsDualizingModuleOf.restrict` — **[Stacks, Tag 0AWH]**: for an open `U`, the
  degree `n_U` of a dualizing module `ω_U` of `K|_U` satisfies `n ≤ n_U`; if `n = n_U` then
  `ω|_U ≅ ω_U`; if `n < n_U` then `ω|_U = 0 ≠ ω_U`.
* `Stacks.Duality.associatedShiftFunction_restrict` — the dimension function of
  [Stacks, Tag 0AWF] attached to `K|_U` is the restriction of the one attached to `K`.
* `Stacks.Duality.IsDualizingModuleOf.restrict_of_associatedShiftFunction_genericPoints` —
  **[Stacks, Tag 0AWH]**: if that dimension function takes one value at all generic points of
  `X`, then `n_U = n` and `ω|_U ≅ ω_U` for every nonempty open `U`.

## The proof

Restriction to an open is exact, so it commutes with cohomology. By
`Stacks.Duality.isGreatest_neg_of_isDualizingModuleOf`, `-n` and `-n_U` are the maximal values of
the dimension functions of `K` and of `K|_U`; the second is the restriction of the first, which
is read off the first nonvanishing stalk of the cohomology sheaves. A dimension function
decreases along specializations and every point specializes from a generic point of `X` which
lies in any open containing it, so if the function is constant, `c` say, on generic points, then
its maximum on `X` and on any nonempty open is `c`.

## References

* [Stacks Project, Tag 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w w'

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **Stacks Project, Tag 0AWH, the first warning.** Let `ω` be a dualizing module of the
dualizing complex `K` on `X`, realized in degree `n`, let `U ⊆ X` be open and let `ω_U` be a
dualizing module of the restriction `K|_U`, realized in degree `n_U`. Then `n ≤ n_U`; if
`n = n_U` then `ω|_U ≅ ω_U`; and if the degree changes, `n < n_U`, then `ω|_U` is zero while `ω_U`
is not, so `ω|_U` is not isomorphic to `ω_U`. -/
@[stacks 0AWH "the section's first warning: the integer n may change on passing to an open U, \
and then the restriction of omega_X to U is not omega_U. The degree can only go up, the two \
modules agree when it does not change, and when it changes the restriction is zero while omega_U \
is not"]
theorem IsDualizingModuleOf.restrict {ω : X.Modules} {K : DerivedCategory X.Modules} {n : ℤ}
    (h : IsDualizingModuleOf ω K n) (U : X.Opens) [HasDerivedCategory.{w'} U.toScheme.Modules]
    {ωU : U.toScheme.Modules} {nU : ℤ}
    (hU : IsDualizingModuleOf ωU
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) nU) :
    n ≤ nU ∧ (n = nU → Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj ω ≅ ωU)) ∧
      (n < nU → IsZero ((Scheme.Modules.restrictFunctor U.ι).obj ω) ∧ ¬ IsZero ωU ∧
        IsEmpty ((Scheme.Modules.restrictFunctor U.ι).obj ω ≅ ωU)) := by
  let e : ∀ i : ℤ, (DerivedCategory.homologyFunctor U.toScheme.Modules i).obj
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) ≅
        (Scheme.Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) := fun i =>
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso i).app K
  have hle : n ≤ nU := by
    by_contra hlt
    exact hU.nonzero ((Functor.map_isZero _ (h.isZero_of_lt nU (by omega))).of_iso (e nU))
  refine ⟨hle, fun heq => ⟨?_⟩, fun hlt => ?_⟩
  · subst heq
    exact eqToIso (by rw [h.eq_homology]) ≪≫ (e n).symm ≪≫ eqToIso hU.eq_homology.symm
  · have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj ω) := by
      rw [h.eq_homology]
      exact (hU.isZero_of_lt n hlt).of_iso (e n).symm
    have hnz : ¬ IsZero ωU := by
      rw [hU.eq_homology]
      exact hU.nonzero
    exact ⟨hz, hnz, ⟨fun f => hnz (hz.of_iso f.symm)⟩⟩

/-- The stalk at `x` of the restriction of a module along an open immersion `j` vanishes exactly
when the stalk at `j x` does. -/
theorem isZero_modulesStalkFunctor_restrict_iff {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (G : Z.Modules) (y : Y) :
    IsZero ((modulesStalkFunctor y).obj ((Scheme.Modules.restrictFunctor j).obj G)) ↔
      IsZero ((modulesStalkFunctor (j y)).obj G) := by
  have e := ((Scheme.Modules.restrictStalkNatIso j y).app G).isZero_iff
  rw [AddCommGrpCat.isZero_iff_subsingleton, AddCommGrpCat.isZero_iff_subsingleton] at e
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact e

/-- **The dimension function of a dualizing complex is compatible with restriction to an open
subscheme**: at a point of `U`, the function of [Stacks, Tag 0AWF] attached to `K|_U` takes the
value of the one attached to `K`. Both are read off the first nonvanishing stalk of the
cohomology sheaves, and the stalks and the local rings of `U` are those of `X`. -/
theorem associatedShiftFunction_restrict {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (U : X.Opens) [HasDerivedCategory.{w'} U.toScheme.Modules]
    (hKU : IsDualizingComplex ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K))
    (x : U.toScheme) :
    associatedShiftFunction ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) x =
      associatedShiftFunction K (U.ι x) := by
  obtain ⟨d, hd⟩ := exists_natCast_ringKrullDim_stalk (U.ι x)
  have hdU : ringKrullDim (U.toScheme.presheaf.stalk x) = (d : WithBot ℕ∞) := by
    rw [← hd]
    exact ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv.symm
  have hst : ∀ j : ℤ, IsZero ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor U.toScheme.Modules j).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K))) ↔
      IsZero ((modulesStalkFunctor (U.ι x)).obj
        ((DerivedCategory.homologyFunctor X.Modules j).obj K)) := fun j =>
    (((modulesStalkFunctor x).mapIso
      (((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryHomologyIso j).app K)).isZero_iff
      ).trans (isZero_modulesStalkFunctor_restrict_iff U.ι _ x)
  rw [associatedShiftFunction_eq_of_stalk_homology hKU x d hdU _
    (fun hz => not_isZero_stalk_homology_of_isDualizingComplex hK (U.ι x) d hd ((hst _).mp hz))
    fun j hj => (hst j).mpr (isZero_stalk_homology_of_lt hK (U.ι x) d hd j hj)]
  ring

/-- Every point of a quasi-sober space is a specialization of a generic point of an irreducible
component. -/
theorem exists_mem_genericPoints_specializes {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (y : T) : ∃ ξ ∈ genericPoints T, ξ ⤳ y := by
  obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := y)).closure
  have hgen := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  refine ⟨hZ.1.genericPoint, ?_, specializes_iff_mem_closure.mpr ?_⟩
  · change closure {_} ∈ irreducibleComponents T
    rw [hgen.def]
    exact hZ
  · rw [hgen.def]
    exact hyZ (subset_closure rfl)

/-- **Stacks Project, Tag 0AWH, the closing remark on the first warning.** If the dimension
function attached to `K` ([Stacks, Tag 0AWF]) takes the same value at every generic point of `X`,
then the degree of the dualizing module does not change on passing to a nonempty open `U ⊆ X`,
and the restriction of the dualizing module of `K` is the dualizing module of `K|_U`. -/
@[stacks 0AWH "the section's closing remark on the first warning: if the dimension function \
attached to omega_X^bullet (Tag 0AWF) maps every generic point of X to the same integer, the \
degree does not change on a nonempty open U and omega_X restricted to U is omega_U"]
theorem IsDualizingModuleOf.restrict_of_associatedShiftFunction_genericPoints
    {ω : X.Modules} {K : DerivedCategory X.Modules} {n : ℤ}
    (h : IsDualizingModuleOf ω K n)
    (hgen : ∃ c : ℤ, ∀ ξ ∈ genericPoints X, associatedShiftFunction K ξ = c)
    (U : X.Opens) (hne : (U : Set X).Nonempty) [HasDerivedCategory.{w'} U.toScheme.Modules]
    {ωU : U.toScheme.Modules} {nU : ℤ}
    (hU : IsDualizingModuleOf ωU
      ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K) nU) :
    nU = n ∧ Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj ω ≅ ωU) := by
  obtain ⟨c, hc⟩ := hgen
  obtain ⟨-, -, δ, hδ⟩ :=
    isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction h.isDualizingComplex
  have hle : ∀ y : X, associatedShiftFunction K y ≤ c := by
    intro y
    obtain ⟨ξ, hξ, hξy⟩ := exists_mem_genericPoints_specializes y
    rw [← hc ξ hξ, ← hδ, ← hδ]
    by_cases hy : ξ = y
    · rw [hy]
    · exact (δ.strictAnti_specializes hξy hy).le
  obtain ⟨u, hu⟩ := hne
  obtain ⟨ξ, hξ, hξu⟩ := exists_mem_genericPoints_specializes u
  have hξU : ξ ∈ (U : Set X) := hξu.mem_open U.isOpen hu
  have hX := isGreatest_neg_of_isDualizingModuleOf h
  have hUg := isGreatest_neg_of_isDualizingModuleOf hU
  have hn : -n = c := by
    refine le_antisymm ?_ (hc ξ hξ ▸ hX.2 ⟨ξ, rfl⟩)
    obtain ⟨⟨y, hy⟩, -⟩ := hX
    rw [← hy]
    exact hle y
  have hres := associatedShiftFunction_restrict h.isDualizingComplex U hU.isDualizingComplex
  have hnU : -nU = c := by
    refine le_antisymm ?_ ?_
    · obtain ⟨⟨y, hy⟩, -⟩ := hUg
      rw [← hy, hres]
      exact hle _
    · calc c = associatedShiftFunction K ξ := (hc ξ hξ).symm
        _ = associatedShiftFunction K (U.ι ⟨ξ, hξU⟩) := rfl
        _ = _ := (hres ⟨ξ, hξU⟩).symm
        _ ≤ -nU := hUg.2 ⟨_, rfl⟩
  exact ⟨by omega, (h.restrict U hU).2.1 (by omega)⟩

end Stacks.Duality

end
