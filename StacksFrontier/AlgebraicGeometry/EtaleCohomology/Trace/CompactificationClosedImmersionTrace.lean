module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationIntegralComparison

/-!
# The canonical Frobenius trace along a closed immersion of compactifications

Let `X` be a scheme over a finite field `k` with two compactifications `j : X ⟶ X̄` and
`j' : X ⟶ X̄'` over `k`, and `g : X̄ ⟶ X̄'` a closed immersion over `k` with `j' = g ∘ j` and
`X = g⁻¹(X)` (for instance the scheme-theoretic closure of `X` in `X̄'`).  For a bounded below
complex `K` of sheaves of `Λ`-modules on `X`, `j'_! K ≅ g_*(j_! K)`
(`Stacks.EtaleCohomology.extensionByZeroIntegralCartesianIso`), so `RΓ_c(X_k̄, K)` computed
through `X̄'` is perfect exactly when it is through `X̄`, and the canonical Frobenius traces agree
(`Stacks.EtaleCohomology.perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage`).
This lets the proof of [Stacks, Tag 03UG] replace an arbitrary compactification by the closure
of `X` in it.

## Main results

* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_eq_of_isClosedImmersion`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} (c c' : CompactificationOf (Over.mk f)) (g : c.space ⟶ c'.space)
  [IsClosedImmersion g] (hbase : g ≫ c'.toBase = c.toBase)
  (sq : IsPullback (𝟙 X) c.immersion c'.immersion g)
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The closed immersion `g : X̄ ⟶ X̄'` as a morphism over `k`. -/
abbrev compactificationSpaceOverHom : Over.mk c.toBase ⟶ Over.mk c'.toBase := Over.homMk g hbase

/-- The underlying morphism of `compactificationSpaceOverHom` is a closed immersion. -/
instance : IsClosedImmersion (compactificationSpaceOverHom c c' g hbase).left :=
  inferInstanceAs (IsClosedImmersion g)

include sq in
/-- `j'_! K ≅ g_*(j_! K)`, degreewise. -/
def extensionByZeroCompactificationComplexIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleExtensionByZero.{u, 0} Λ c'.immersion).mapCochainComplexPlus.obj K ≅
      (etaleModuleDirectImage.{u, 0} Λ
          (compactificationSpaceOverHom c c' g hbase).left).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ c.immersion).mapCochainComplexPlus.obj K) :=
  mapCochainComplexPlusIsoOfNatIso
    (extensionByZeroIntegralCartesianIso Λ c.immersion c'.immersion g sq).symm K

include hbase sq in
/-- **The canonical Frobenius trace does not change along a closed immersion of
compactifications** `g : X̄ ⟶ X̄'` with `X = g⁻¹(X)`: if `RΓ_c(X_k̄, K)` through `X̄'` is perfect,
so is it through `X̄`, and the two traces of `π_X^*` agree. -/
theorem canonicalCompactSupportLefschetzNumber_eq_of_isClosedImmersion [Finite Λ]
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hc' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ f c' kbar K))) :
    ∃ hc : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ f c kbar K)),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ f c kbar p q hcard K hc =
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ f c' kbar p q hcard K hc' := by
  have hY := isPerfect_frobeniusRestriction_of_iso Λ (Over.mk c'.toBase) kbar
    (extensionByZeroCompactificationComplexIso Λ c c' g hbase sq K) hc'
  have hc := (isPerfect_frobeniusRestriction_directImage_iff Λ
    (compactificationSpaceOverHom c c' g hbase) kbar _).1 hY
  exact ⟨hc, ((perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ
    (Over.mk c'.toBase) kbar p q hcard
    (extensionByZeroCompactificationComplexIso Λ c c' g hbase sq K) hc' hY).trans
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage Λ
      (compactificationSpaceOverHom c c' g hbase) p q hcard kbar _ hY hc)).symm⟩

end Stacks.EtaleCohomology

end
