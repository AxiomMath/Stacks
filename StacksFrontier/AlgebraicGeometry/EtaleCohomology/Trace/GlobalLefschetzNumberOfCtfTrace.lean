module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The global Lefschetz number of an object of `D_ctf(X, Λ)`

Let `Λ` be a finite ring, `X` a projective curve over a finite field `k` with `q = p ^ f`
elements, `k̄` an algebraic closure of `k` and `K ∈ D_ctf(X, Λ)`. There is a canonical map
`c_K : π_X^{-1} K ⟶ K`, and its base change `c_K|_{X_k̄}` induces an action `π_X^*` on the perfect
complex `RΓ(X_k̄, K|_{X_k̄})`. The global Lefschetz number of `K` is the trace
`Tr(π_X^* | RΓ(X_k̄, K))` of that action, an element of `Λ^natural` ([Stacks, Tag 03TX]).

## Main definitions

* `Stacks.EtaleCohomology.ctfFrobeniusActionOnCohomology` — the perfect complex
  `RΓ(X_k̄, K|_{X_k̄})` with the action `π_X^*`.
* `Stacks.EtaleCohomology.globalLefschetzNumberOfCtf` — **[Stacks, Tag 03TX]**, the global
  Lefschetz number `Tr(π_X^* | RΓ(X_k̄, K|_{X_k̄}))` in `Λ^natural`.

## Main results

* `Stacks.EtaleCohomology.globalLefschetzNumberOfCtf_eq_perfectDerivedTrace` — it is the trace
  of `π_X^*` on the perfect complex `RΓ(X_k̄, K|_{X_k̄})`.
* `Stacks.EtaleCohomology.globalLefschetzNumberOfCtf_eq_alternatingTrace` — it is computed on any
  bounded complex of finite projective modules representing `RΓ(X_k̄, K|_{X_k̄})`
  ([Stacks, Tag 03TI]).
* `Stacks.EtaleCohomology.globalLefschetzNumberOfCtf_congr` — isomorphic objects of
  `D_ctf(X, Λ)` have the same global Lefschetz number.

## Implementation notes

`Λ` is an arbitrary finite ring, possibly noncommutative, as in the source; `D_ctf(X, Λ)` is
`Stacks.EtaleCohomology.IsCtf`, which is formulated for such a ring. An object of it is bounded,
and it is taken in the bounded below derived category, where `RΓ(X_k̄, -)` is defined. `k̄` is an
algebraic closure of `k`. Neither `RΓ(X_k̄, K|_{X_k̄})` nor `π_X^*` is supplied as data: both are
computed from `X`, `k̄` and `K`. The action is
`Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo`, induced by the base change of the
canonical map of [Stacks, Tag 03SR], and perfectness is [Stacks, Tag 03TV],
`Stacks.EtaleCohomology.isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf`.

This lives in its own file, apart from the construction of `π_X^*`, so that importing the
construction does not import the proof of [Stacks, Tag 03TV].

## References

* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TI](https://stacks.math.columbia.edu/tag/03TI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/- The import of `Stacks.EtaleCohomology.hasSheafifyEtale`, a sheafification instance pinned to the
module universe `u + 1`, would otherwise be tried first for `EtaleModules Λ X`, whose module
universe is `max (u + 1) r`; the universe-polymorphic instance is preferred. -/
attribute [local instance high] etaleModules_hasSheafify

/-! ### The global Lefschetz number -/

section Lefschetz

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] [Fintype k] (gk : X.obj ⟶ Spec (.of k))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The perfect complex `RΓ(X_k̄, K|_{X_k̄})` with the action `π_X^*` on it**, for a projective
curve `X` over the finite field `k` and `K ∈ D_ctf(X, Λ)`: the derived global sections of the
restriction of `K` to `X_k̄`, perfect by [Stacks, Tag 03TV], with the endomorphism
`Stacks.EtaleCohomology.frobeniusGlobalSectionsEndo` induced by the base change of the canonical
map `c_K : π_X^{-1} K ⟶ K`. -/
@[sga "5 XII 6.1" "special case"]
public def ctfFrobeniusActionOnCohomology (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K)) :
    FrobeniusActionOnCohomology.{r, max (u + 1) r} Λ where
  cohomology := ⟨_, isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf
    B X Λ gk kbar hcurve hproj K hK⟩
  frobeniusAction := DerivedCategory.Plus.ι.map
    (frobeniusGlobalSectionsEndo.{u, r} Λ (Over.mk gk) kbar p q hcard K)

/-- **Stacks, Tag 03TX: the global Lefschetz number of `K`.** Let `Λ` be a finite, possibly
noncommutative, ring, `X` a projective curve over a finite field `k` with `p ^ q` elements, `k̄`
an algebraic closure of `k` and `K ∈ D_ctf(X, Λ)`. The base change `c_K|_{X_k̄}` of the canonical
map `c_K : π_X^{-1} K ⟶ K` induces an action `π_X^*` on the perfect complex
`RΓ(X_k̄, K|_{X_k̄})`; the global Lefschetz number of `K` is its trace
`Tr(π_X^* | RΓ(X_k̄, K|_{X_k̄}))`, an element of `Λ^natural`.

`D_ctf(X, Λ)` is `Stacks.EtaleCohomology.IsCtf`, which makes sense for a noncommutative `Λ`; an
object of it is bounded, so it is taken in the bounded below derived category, on which
`RΓ(X_k̄, -)` is defined. Perfectness of `RΓ(X_k̄, K|_{X_k̄})` is [Stacks, Tag 03TV], proved, not
assumed. -/
@[stacks 03TX]
public def globalLefschetzNumberOfCtf (hcurve : IsCurve k gk)
    (hproj : IsProjective gk) (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K)) :
    CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient Λ :=
  globalLefschetzNumber.{r, max (u + 1) r} Λ
    (ctfFrobeniusActionOnCohomology.{u, r} B X Λ gk kbar p q hcard hcurve hproj K hK)

/-- The global Lefschetz number of `K` is the trace of `π_X^*` on the perfect complex
`RΓ(X_k̄, K|_{X_k̄})`. -/
public theorem globalLefschetzNumberOfCtf_eq_perfectDerivedTrace
    (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K)) :
    globalLefschetzNumberOfCtf.{u, r} B X Λ gk kbar p q hcard hcurve hproj K hK =
      CategoryTheory.FilteredDerived.perfectDerivedTrace Λ
        ⟨_, isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf
          B X Λ gk kbar hcurve hproj K hK⟩
        (DerivedCategory.Plus.ι.map
          (frobeniusGlobalSectionsEndo.{u, r} Λ (Over.mk gk) kbar p q hcard K)) :=
  rfl

/-- **Well-definedness: the trace is computed on any representative.** The global Lefschetz
number of `K` is the alternating sum of the traces of any cochain endomorphism representing
`π_X^*` on any bounded complex of finite projective `Λ`-modules representing
`RΓ(X_k̄, K|_{X_k̄})` ([Stacks, Tag 03TI]). -/
public theorem globalLefschetzNumberOfCtf_eq_alternatingTrace
    (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    (K : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj))
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K))
    (P : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ)
    (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex Λ P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk gk) kbar)).obj
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ (Over.mk gk) kbar).obj K)))
    (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫ DerivedCategory.Plus.ι.map
      (frobeniusGlobalSectionsEndo.{u, r} Λ (Over.mk gk) kbar p q hcard K) ≫ e.inv) :
    globalLefschetzNumberOfCtf.{u, r} B X Λ gk kbar p q hcard hcurve hproj K hK =
      CategoryTheory.FilteredDerived.alternatingTrace Λ P hP g :=
  globalLefschetzNumber_eq_alternatingTrace.{r, max (u + 1) r} Λ _ P hP e g hg

/-- **Well-definedness: invariance under isomorphism.** Isomorphic objects of `D_ctf(X, Λ)` have
the same global Lefschetz number: an isomorphism `K ≅ L` induces an isomorphism of
`RΓ(X_k̄, K|_{X_k̄})` with `RΓ(X_k̄, L|_{X_k̄})` intertwining the two actions `π_X^*`, by
naturality of `π_X^*`. -/
public theorem globalLefschetzNumberOfCtf_congr
    (hcurve : IsCurve k gk) (hproj : IsProjective gk)
    {K L : DerivedCategory.Plus (EtaleModules.{u, r} Λ X.obj)} (e : K ≅ L)
    (hK : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj K))
    (hL : IsCtf.{u, r} B X Λ (DerivedCategory.Plus.ι.obj L)) :
    globalLefschetzNumberOfCtf.{u, r} B X Λ gk kbar p q hcard hcurve hproj K hK =
      globalLefschetzNumberOfCtf.{u, r} B X Λ gk kbar p q hcard hcurve hproj L hL := by
  refine CategoryTheory.FilteredDerived.perfectDerivedTrace_congr Λ _ _
    (DerivedCategory.Plus.ι.mapIso
      ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk gk) kbar)).mapIso
        ((fieldBaseChangeDerivedRestriction.{u, r} Λ (Over.mk gk) kbar).mapIso e))) _ _ ?_
  have h := congrArg DerivedCategory.Plus.ι.map
    (frobeniusGlobalSectionsEndo_naturality.{u, r} Λ (Over.mk gk) kbar p q hcard e.hom)
  simp only [Functor.map_comp] at h
  exact h.symm

end Lefschetz

/- The declaration lives in `CurveGlobalSectionsPerfect`, which does not carry the attribute;
the registration is recorded here. -/
add_to_stacks 03TV "for a projective curve `X` over a field `k`, a finite ring `Λ` and `K` in
  `D_ctf(X, Λ)`, `RΓ(X_k̄, K)` is a perfect complex of `Λ`-modules"
  Stacks.EtaleCohomology.isPerfect_etaleModuleDerivedGlobalSections_fieldBaseChange_of_isCtf

end Stacks.EtaleCohomology

end
