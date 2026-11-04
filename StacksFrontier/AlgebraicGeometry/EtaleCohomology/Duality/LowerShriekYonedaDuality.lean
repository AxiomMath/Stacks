module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekDualityTranspose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzeroLowerShriek

/-!
# Poincaré duality for complexes over the base field, read on a compactification

Let `g : V → Spec k` have a compactification `j : V → X̄`, `Λ = ℤ/N`, and let `D₀`, `F` be sheaves
of `Λ`-modules on `V_ét`. For a trace `t : Ext^n_X̄(Λ, j_! D₀) → Λ` the trace
`Stacks.EtaleCohomology.lowerShriekTrace` on `Hom_{D⁺(k)}(Λ_k[0], Rg_!(D₀[0])[n])` is `t` read
through `Hom(Λ_k[0], Rg_! -) ≅ Hom(Λ_X̄[0], Rj_! -)`
(`Stacks.EtaleCohomology.lowerShriekCoyonedaIso`), `Rj_!(D₀[0]) ≅ (j_! D₀)[0]` and
`Ext^n ≅ Hom_{D⁺}(-[0], -[0][n])`. Then duality for the homological functor
`Hom(Λ_k[0], Rg_! -)` on `D⁺(V)` at `F[0]`, with dualizing object `D₀[0]`
(`Stacks.HomologicalDuality.IsPerfect`), is Yoneda duality on `X̄`:
`Ext^i_X̄(Λ, j_! F) × Ext^{n-i}_X̄(j_! F, j_! D₀) → Ext^n_X̄(Λ, j_! D₀) → Λ` is perfect
(`Stacks.EtaleCohomology.isDualityPerfect_of_isPerfect_lowerShriek`), and conversely when the
groups `Ext^q_X̄(Λ, j_! F)` and `Ext^q_X̄(j_! F, j_! D₀)` vanish for `q > n`
(`Stacks.EtaleCohomology.isPerfect_lowerShriek_of_isDualityPerfect`). Here `j_!` is bijective on
`Ext` since the unit of `j_! ⊣ j⁻¹` is invertible.

Over the base field duality on `V` can be moved along a factorization `g = q ∘ f` (the Leray
isomorphism `R(q ∘ f)_! ≅ Rq_! ∘ Rf_!`); this is how Poincaré duality on an elementary fibration
is reduced to duality on its base, in the fibration step of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rg_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main definitions

* `Stacks.EtaleCohomology.lowerShriekTrace`.

## Main results

* `Stacks.EtaleCohomology.isDualityPerfect_of_isPerfect_lowerShriek`.
* `Stacks.EtaleCohomology.isPerfect_lowerShriek_of_isDualityPerfect`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

variable {k : Type u} [Field k] {V : Scheme.{u}} (g : V ⟶ Spec (.of k))
  (jc : CompactificationOf (Over.mk g)) (N : ℕ) (D₀ : EtaleModules.{u, 0} (ZMod N) V) (n : ℕ)

/-- **The trace on compactly supported cohomology over the base field** induced by a trace
`t : Ext^n_X̄(Λ, j_! D₀) → Λ` on a compactification `j : V → X̄`: the map
`Hom_{D⁺(k)}(Λ_k[0], Rg_!(D₀[0])[n]) ≅ Hom_{D⁺(X̄)}(Λ_X̄[0], Rj_!(D₀[0])[n])
≅ Ext^n_X̄(Λ, j_! D₀) → Λ`. -/
def lowerShriekTrace
    (t : Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n →+ ZMod N) :
    (derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N)))).obj
      (((DerivedCategory.Plus.singleFunctor _ 0).obj D₀)⟦(n : ℤ)⟧) →+ ZMod N :=
  (HomologicalDuality.transferTrace (etaleModuleDerivedExtensionByZero.{u, 0} (ZMod N) jc.immersion)
    (Iso.refl _) (HomologicalDuality.degreeZeroTheta _ (isLE_extensionByZero_single g jc N)
      (isGE_extensionByZero_single g jc N) _ (extensionByZeroTopHomologyIso g jc N) D₀)
    (add_zero (n : ℤ))
    (t.comp (HomologicalDuality.extPlusAddEquiv _ _ n).symm.toAddMonoidHom)).comp
    ((lowerShriekCoyonedaIso g jc N).hom.app _).hom

/-- `j_!` is bijective on `Ext`, the unit of `j_! ⊣ j⁻¹` being invertible. -/
theorem bijective_mapExactFunctor_extensionByZero (F : EtaleModules.{u, 0} (ZMod N) V) (m : ℕ) :
    Function.Bijective (fun e : Ext F D₀ m =>
      (e.mapExactFunctor (etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion) :
        Ext _ _ m)) :=
  Stacks.ExtAdjunction.mapExtAddHom_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod N) jc.immersion) F D₀ m

/-- Precomposing a map on `Ext` with the inverse of `extPlusAddEquiv` recovers it on `extPlus`. -/
private theorem comp_extPlusAddEquiv_symm_extPlus {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    [HasDerivedCategory 𝒜] [HasExt.{u} 𝒜] {X Y : 𝒜} {m : ℕ} {M : Type*} [AddCommGroup M]
    (t : Ext.{u} X Y m →+ M) (x : Ext.{u} X Y m) :
    (t.comp (HomologicalDuality.extPlusAddEquiv X Y m).symm.toAddMonoidHom)
      (HomologicalDuality.extPlusAddEquiv X Y m x) = t x :=
  congrArg t ((HomologicalDuality.extPlusAddEquiv _ _ m).symm_apply_apply x)

/-- **Duality over the base field gives Yoneda duality on the compactification**: if duality holds
for `Hom(Λ_k[0], Rg_! -)` at `F[0]`, with dualizing object `D₀[0]` and the trace induced by `t`,
then `Ext^i_X̄(Λ, j_! F) × Ext^{n-i}_X̄(j_! F, j_! D₀) → Ext^n_X̄(Λ, j_! D₀) → Λ` is perfect. -/
theorem isDualityPerfect_of_isPerfect_lowerShriek
    (t : Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n →+ ZMod N)
    (F : EtaleModules.{u, 0} (ZMod N) V)
    (h : HomologicalDuality.IsPerfect (derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj D₀) (n : ℤ) (lowerShriekTrace g jc N D₀ n t)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :
    Ext.IsDualityPerfect (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj F) :=
  HomologicalDuality.isDualityPerfect_of_isPerfect_degreeZero _
    (isLE_extensionByZero_single g jc N) (isGE_extensionByZero_single g jc N) _
    (extensionByZeroTopHomologyIso g jc N) D₀ _ n _ t
    (comp_extPlusAddEquiv_symm_extPlus t) F
    (bijective_mapExactFunctor_extensionByZero g jc N D₀ F)
    ((HomologicalDuality.isPerfect_iff_of_natIso (lowerShriekCoyonedaIso g jc N) _ _ _ _).1 h)

/-- **Yoneda duality on the compactification gives duality over the base field**, when moreover
`Ext^q_X̄(Λ, j_! F) = 0` and `Ext^q_X̄(j_! F, j_! D₀) = 0` for `q > n`. -/
theorem isPerfect_lowerShriek_of_isDualityPerfect
    (t : Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n →+ ZMod N)
    (F : EtaleModules.{u, 0} (ZMod N) V)
    (hF : Ext.IsDualityPerfect (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) n t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj F))
    (hO : ∀ q : ℕ, n < q → Subsingleton (Ext (ExtensionTorsor.unitSheaf (X := jc.space) N)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj F) q))
    (hD : ∀ q : ℕ, n < q → Subsingleton (Ext
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj F)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod N) jc.immersion).obj D₀) q)) :
    HomologicalDuality.IsPerfect (derivedLowerShriek.{u, 0} g jc (ZMod N) ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (ExtensionTorsor.unitSheaf (X := Spec (.of k)) N))))
      ((DerivedCategory.Plus.singleFunctor _ 0).obj D₀) (n : ℤ) (lowerShriekTrace g jc N D₀ n t)
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
  (HomologicalDuality.isPerfect_iff_of_natIso (lowerShriekCoyonedaIso g jc N) _ _ _ _).2
    (HomologicalDuality.isPerfect_degreeZero_of_isDualityPerfect _
      (isLE_extensionByZero_single g jc N) (isGE_extensionByZero_single g jc N) _
      (extensionByZeroTopHomologyIso g jc N) D₀ _ n _ t
      (comp_extPlusAddEquiv_symm_extPlus t) F
      (bijective_mapExactFunctor_extensionByZero g jc N D₀ F) hF hO hD)

end Stacks.EtaleCohomology

end
