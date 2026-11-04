module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans

/-!
# `RΓ_c` of an open subscheme, Frobenius-equivariantly

Let `j : X ⟶ X̄` be a compactification of `X` over a finite field `k` and `j_U : U ⟶ X` an open
immersion.  The composite `j ∘ j_U` is a compactification of `U`
(`AlgebraicGeometry.CompactificationOf.restrictOpen`), with the same scheme `X̄` proper over `k`,
and extension by zero composes, `(j ∘ j_U)_! ≅ j_! ∘ j_{U!}`.  Hence

```
RΓ_c(U_k̄, K) = RΓ(X̄_k̄, ((j ∘ j_U)_! K)|_{X̄_k̄})
  ≅ RΓ(X̄_k̄, (j_! j_{U!} K)|_{X̄_k̄}) = RΓ_c(X_k̄, j_{U!} K),
```

and the canonical geometric Frobenius `π^*` of both sides is the canonical endomorphism of
`RΓ(X̄_k̄, (-)|_{X̄_k̄})` attached to the same `X̄`, which is natural in the complex on `X̄`; so
the identification is `π^*`-equivariant.  This is the open half of the excision step of the
reduction of the weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH))
to curves: the first term of the sequence `0 → j_{U!} j_U⁻¹ F → F → i_* i⁻¹ F → 0` computes the
compactly supported cohomology of `U`.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroCompPlusIso`: the isomorphism
  `(j ∘ j_U)_! K ≅ j_! (j_{U!} K)` of bounded below complexes.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictOpenIso`: the isomorphism
  `RΓ_c(U_k̄, K) ≅ RΓ_c(X_k̄, j_{U!} K)`.

## Main results

* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyRestrictOpenIso_hom_frobenius`: the
  identification commutes with the canonical Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) {U : Scheme.{u}} (jU : U ⟶ X)
  [IsOpenImmersion jU] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- Extension by zero composes, degreewise on a bounded below complex:
`(j ∘ j_U)_! K ≅ j_! (j_{U!} K)`. -/
public def extensionByZeroCompPlusIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    (etaleModuleExtensionByZero.{u, 0} Λ (jU ≫ j.immersion)).mapCochainComplexPlus.obj K ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K) where
  hom := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).hom (ComplexShape.up ℤ)).app K.obj)
  inv := ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).inv (ComplexShape.up ℤ)).app K.obj)
  hom_inv_id := by
    ext n : 2
    exact (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).hom_inv_id_app _
  inv_hom_id := by
    ext n : 2
    exact (etaleModuleExtensionByZeroCompIso.{u, 0} Λ jU j.immersion).inv_hom_id_app _

/-- **`RΓ_c(U_k̄, K) ≅ RΓ_c(X_k̄, j_{U!} K)`** for the compactification `j ∘ j_U` of `U` induced by
a compactification `j` of `X`. -/
public def compactSupportFrobeniusCohomologyRestrictOpenIso
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    compactSupportFrobeniusCohomology.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar K ≅
      compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K) :=
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapIso
      ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ (Over.mk j.toBase) kbar).mapIso
        (extensionByZeroCompPlusIso Λ f j jU K)))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(U_k̄, K) ≅ RΓ_c(X_k̄, j_{U!} K)` commutes with the canonical
geometric Frobenius.** -/
public theorem compactSupportFrobeniusCohomologyRestrictOpenIso_hom_frobenius
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) :
    canonicalCompactSupportFrobenius.{u, 0} Λ (jU ≫ f) (j.restrictOpen jU) kbar p q hcard K ≫
        (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f j jU kbar K).hom =
      (compactSupportFrobeniusCohomologyRestrictOpenIso Λ f j jU kbar K).hom ≫
        canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleExtensionByZero.{u, 0} Λ jU).mapCochainComplexPlus.obj K) :=
  (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) (Over.mk j.toBase) kbar p q hcard
    (extensionByZeroCompPlusIso Λ f j jU K).hom).symm

end Stacks.EtaleCohomology

end
