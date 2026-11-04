module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisActionFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapFixedPointTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois action on `RΓ_c(X_k̄, K)`

Let `k` be a field, `k̄` an extension field of `k`, `X` a scheme over `k` and `j : X ⟶ X̄` a
compactification of `X` over `k`.  The Trace Formula chapter defines (Remark 03UI (2))

`RΓ_c(X_k̄, K) := RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`,

and a `k`-automorphism `σ` of `k̄` acts on it.  The action comes from `X̄` being defined over `k`:
`s_σ = id_{X̄} × Spec σ` is an automorphism of `X̄_k̄` over `X̄`
(`Stacks.Frobenius.galoisBaseChange`), so the restriction `L|_{X̄_k̄}` of a sheaf `L` on `X̄`
carries a canonical map `L|_{X̄_k̄} ⟶ (s_σ)_*(L|_{X̄_k̄})`, adjoint to the unit of restriction
along `pr : X̄_k̄ ⟶ X̄` and the identification `(s_σ ≫ pr)_* = pr_*`: the twist
`Stacks.EtaleCohomology.selfMapTwist` of the endomorphism `s_σ` of `X̄_k̄` over `X̄`.  Applying
`RΓ(X̄_k̄, -)` and `RΓ(X̄_k̄, (s_σ)_* -) = RΓ(X̄_k̄, -)` gives the endomorphism `σ` of
`RΓ_c(X_k̄, K)`.

## Main definitions

* `Stacks.EtaleCohomology.galoisRestrictionDerivedMap` — the map
  `C|_{Y_k̄} ⟶ R(s_σ)_*(C|_{Y_k̄})` for a bounded below complex `C` on a `k`-scheme `Y`.
* `Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo` — the induced endomorphism of
  `RΓ(Y_k̄, C|_{Y_k̄})`.
* `Stacks.EtaleCohomology.galoisCompactSupportCohomology` — the complex
  `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` of Remark 03UI (2).
* `Stacks.EtaleCohomology.galoisCompactSupportAction` and
  `Stacks.EtaleCohomology.galoisCompactSupportGroupAction` — the action of `σ` on it and on
  `H^i_c(X_k̄, K)`.

## Implementation notes

`RΓ(X̄_k̄, -)` is the derived global sections on `X̄_k̄` itself, as in the source, rather than
`RΓ(Spec k̄, -) ∘ Rπ_*` for `π : X̄_k̄ ⟶ Spec k̄`: the automorphism `s_σ` lies over `Spec σ`, not
over `Spec k̄`, while it lies over `X̄_k̄ ⟶ X̄`, so global sections on `X̄_k̄` are what it acts on
without a second comparison.  The two agree by `etaleModuleDerivedGlobalSectionsCompIso`.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The Galois action on the cohomology of a restriction -/

section Twist

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The canonical morphism `C|_{Y_k̄} ⟶ R(s_σ)_*(C|_{Y_k̄})`** in the bounded below derived
category: the twist `C|_{Y_k̄} ⟶ (s_σ)_*(C|_{Y_k̄})` of
`Stacks.EtaleCohomology.selfMapComplexTwist` for the automorphism `s_σ` of `Y_k̄` over `Y`,
followed by the comparison of the degreewise direct image with the derived direct image. -/
public def galoisRestrictionDerivedMap
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    fieldBaseChangeRestriction.{u, r} Λ Y kbar C ⟶
      (etaleModuleDerivedDirectImage.{u, r} Λ (galoisBaseChange Y kbar σ)).obj
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) :=
  DerivedCategory.Plus.Q.map
      (selfMapComplexTwist.{u, r} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
        (galoisBaseChange_comp_fst Y kbar σ) C) ≫
    (Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, r} Λ (galoisBaseChange Y kbar σ))).app
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)

/-- **The action of `σ` on `RΓ(Y_k̄, C|_{Y_k̄})`**: `RΓ(Y_k̄, -)` of the canonical morphism
`C|_{Y_k̄} ⟶ R(s_σ)_*(C|_{Y_k̄})`, followed by `RΓ(Y_k̄, R(s_σ)_* -) ≅ RΓ(Y_k̄, -)`. -/
public def galoisRestrictionCohomologyEndo
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) ⟶
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ Y kbar C) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
      (galoisRestrictionDerivedMap.{u, r} Λ Y kbar σ C) ≫
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ (galoisBaseChange Y kbar σ)).inv.app
      (fieldBaseChangeRestriction.{u, r} Λ Y kbar C)

end Twist

/-! ### Cohomology with compact support -/

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The complex `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`** of Remark 03UI (2), for a bounded
below complex `K` of sheaves of `Λ`-modules on `X_étale` and a compactification `j : X ⟶ X̄`
over `k`: extension by zero to `X̄`, restriction to `X̄_k̄`, and derived global sections on
`X̄_k̄`. -/
@[sga "4½ Rapport 3.6"]
public abbrev galoisCompactSupportCohomology
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk j.toBase) kbar)).obj
    (fieldBaseChangeRestriction.{u, r} Λ (Over.mk j.toBase) kbar
      ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K))

/-- **The action of `σ ∈ Aut_k(k̄)` on `RΓ_c(X_k̄, K)`**, induced by `id_{X̄} × Spec σ` on the
base change `X̄_k̄` of the compactification. -/
public def galoisCompactSupportAction (σ : kbar ≃ₐ[k] kbar)
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    galoisCompactSupportCohomology.{u, r} Λ f j kbar K ⟶
      galoisCompactSupportCohomology.{u, r} Λ f j kbar K :=
  galoisRestrictionCohomologyEndo.{u, r} Λ (Over.mk j.toBase) kbar σ
    ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K)

/-- **The module `H^i_c(X_k̄, K)`**, the `i`-th cohomology of `RΓ_c(X_k̄, K)`. -/
public abbrev galoisCompactSupportCohomologyGroup
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    ModuleCat.{max (u + 1) r} Λ :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).obj
    (galoisCompactSupportCohomology.{u, r} Λ f j kbar K)

/-- **The action of `σ ∈ Aut_k(k̄)` on `H^i_c(X_k̄, K)`**, induced on cohomology by
`Stacks.EtaleCohomology.galoisCompactSupportAction`. -/
public def galoisCompactSupportGroupAction (σ : kbar ≃ₐ[k] kbar)
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    galoisCompactSupportCohomologyGroup.{u, r} Λ f j kbar K i ⟶
      galoisCompactSupportCohomologyGroup.{u, r} Λ f j kbar K i :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
    (galoisCompactSupportAction.{u, r} Λ f j kbar σ K)

end CompactSupport

end Stacks.EtaleCohomology

end
