module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingGysin
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingFiveLemma
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Poincaré duality passes from a smooth stratum to the sheaves supported on it

Consider a cartesian square of schemes
```
T  --u--> T̄
|i        |ι
W  --j--> X̄
```
with `j`, `u` open and `ι` a closed immersion (so `i` is a closed immersion): `T` is a closed
subscheme of an open `W` of `X̄`, and `T̄` its closure (or any closed subscheme of `X̄` meeting `W`
in `T`). Let `ℓ` be a prime and `Λ = ℤ/ℓ`. Fix a sheaf `D` on `X̄` (a dualizing object:
`j'_! Λ_{W'}` for an open `W ⊆ W'`) and write `D' = j^{-1} D`. A *purity class*
`γ ∈ Ext^c_W(i_* Λ_T, D')` for a sheaf `G` on `T` is one for which `y ↦ i_* y ∘ γ` is bijective
`Ext^q_T(G, Λ_T) → Ext^{q + c}_W(i_* G, D')` for every `q`, with `Ext^q_W(i_* G, D') = 0` for
`q < c`: for `W` smooth, `T` smooth of codimension `c'`, `D' = Λ_W` and `c = 2c'` this is
cohomological purity.

For a trace `t` on `Ext^N_X̄(Λ_X̄, D)` this file identifies duality on `X̄` at
`j_! i_* G = (T → X̄)_! G` (coefficients supported on the stratum `T`) with duality on `T̄` at
`u_! G`, i.e. Poincaré duality on `T` with coefficients `G` and dualizing object `u_! Λ_T`, for
the trace on `H^{N - c}_c(T) = Ext^{N - c}_{T̄}(Λ_T̄, u_! Λ_T)` induced by `t` and the Gysin class
`ι_* u_! Λ_T ≅ j_! i_* Λ_T → j_! j^{-1} D[c] → D[c]`, provided `H^q_c(T, G) = 0` for `q > N - c`.

## Main results

* `Stacks.EtaleCohomology.stratumGysinClass`: the Gysin class on `X̄`.
* `Stacks.EtaleCohomology.stratumTrace`: the induced trace on `H^{N-c}_c(T)`.
* `Stacks.EtaleCohomology.isDualityPerfect_stratum_iff`: duality at `j_! i_* G` on `X̄` iff
  duality at `u_! G` on `T̄`.
* `Stacks.EtaleCohomology.subsingleton_ext_stratum`: the vanishing of `Ext(j_! i_* G, D)` from
  that on `T̄`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize comp_preservesFiniteLimits
  comp_preservesFiniteColimits

variable {ℓ : ℕ} [Fact ℓ.Prime] {T W X Tb : Scheme.{u}} (i : T ⟶ W) (u : T ⟶ Tb) (j : W ⟶ X)
  (ι : Tb ⟶ X) [IsOpenImmersion j] [IsOpenImmersion u] [IsClosedImmersion ι]
  (sq : IsPullback i u j ι) (D : EtaleModules.{u, 0} (ZMod ℓ) X) {N N' c : ℕ} (hN : N' + c = N)

variable [IsClosedImmersion i]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι)]
  (γ : Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj (unitSheaf (X := T) ℓ))
    ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj D) c)
  (t : Ext (unitSheaf (X := X) ℓ) D N →+ ZMod ℓ)

/-- The **Gysin class** `ι_* u_! Λ_T ≅ j_! i_* Λ_T → D[c]` on `X̄` of a class
`γ ∈ Ext^c_W(i_* Λ_T, j^{-1} D)`, through the adjunction `j_! ⊣ j^{-1}`. -/
def stratumGysinClass :
    Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ)))
      D c :=
  (Ext.mk₀ ((etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i u j ι sq).inv.app
    (unitSheaf ℓ))).comp
      (Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j) _ D c γ)
      (zero_add c)

/-- `ι^{-1} Λ_X̄ ≅ Λ_T̄`. -/
def unitSheafInverseImageIsoOfClosed :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) ι).obj (unitSheaf (X := X) ℓ) ≅
      unitSheaf (X := Tb) ℓ :=
  (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) ι).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- The trace on `H^{N'}_c(T) = Ext^{N'}_{T̄}(Λ_T̄, u_! Λ_T)` induced by a trace `t` on
`Ext^N_X̄(Λ_X̄, D)` and the Gysin class of `γ`, `N' + c = N`:
`z ↦ t (η ∘ ι_* z ∘ Γ)`, transported along `ι^{-1} Λ_X̄ ≅ Λ_T̄`. -/
def stratumTrace :
    Ext (unitSheaf (X := Tb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ)) N' →+ ZMod ℓ :=
  Ext.transportTrace (Ext.gysinTrace (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι)
      (unitSheaf (X := X) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ))
      D hN (stratumGysinClass i u j ι sq D γ) t)
    (unitSheafInverseImageIsoOfClosed ι) (Iso.refl _)

omit [IsClosedImmersion i] in
/-- **Poincaré duality passes from a smooth stratum to the sheaves supported on it.** Given a
purity class `γ` for `G` (`y ↦ i_* y ∘ γ` bijective
`Ext^q_T(G, Λ_T) → Ext^{q+c}_W(i_* G, j^{-1} D)` and `Ext^q_W(i_* G, j^{-1} D) = 0` for `q < c`)
and `H^q_c(T, G) = Ext^q_{T̄}(Λ_T̄, u_! G) = 0` for `q > N'`, duality on `X̄` at `j_! i_* G` for
`t` holds if and only if duality on `T̄` at `u_! G` holds for the induced trace `stratumTrace` on
`H^{N'}_c(T)`, `N' + c = N`. -/
theorem isDualityPerfect_stratum_iff (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (hpur : ∀ q, Function.Bijective (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ
        (rfl : q + c = q + c)))
    (hpur₀ : ∀ q, q < c →
      Subsingleton (Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G)
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj D) q))
    (hvan : ∀ q, N' < q → Subsingleton (Ext (unitSheaf (X := Tb) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G) q)) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G)) ↔
      Ext.IsDualityPerfect (unitSheaf (X := Tb) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ)) N'
        (stratumTrace i u j ι sq D hN γ t)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G) := by
  let e := etaleModuleExtensionByZeroDirectImageIso.{u, 0} (ZMod ℓ) i u j ι sq
  let iS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) i
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u
  let ιS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) ι
  let adj := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} (ZMod ℓ) ι
  have := etaleModuleInverseImage_preservesFiniteColimits.{u, 0} (ZMod ℓ) ι
  have h1 : Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t (jS.obj (iS.obj G)) ↔
      Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) D N t (ιS.obj (uS.obj G)) :=
    ⟨Ext.isDualityPerfect_of_iso (e.app G), Ext.isDualityPerfect_of_iso (e.app G).symm⟩
  refine h1.trans ((Ext.isDualityPerfect_obj_iff_gysinTrace adj (unitSheaf (X := X) ℓ)
    (uS.obj (unitSheaf (X := T) ℓ)) D hN (stratumGysinClass i u j ι sq D γ) t
    (uS.obj G) ?_ ?_ ?_).trans
      (Ext.isDualityPerfect_transport_iff _ (unitSheafInverseImageIsoOfClosed ι) (Iso.refl _) _))
  · intro q
    have hU := Stacks.ExtAdjunction.mapExtAddHom_bijective
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) u) G (unitSheaf (X := T) ℓ) q
    rw [← Function.Bijective.of_comp_iff _ hU]
    let adjJ := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j
    have key : ∀ y' : Ext G (unitSheaf (X := T) ℓ) q,
        ((y'.mapExactFunctor uS).mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ)
          (rfl : q + c = q + c) =
        (Ext.mk₀ (e.inv.app G)).comp (Stacks.ExtAdjunction.extMap adjJ (iS.obj G) D (q + c)
          ((y'.mapExactFunctor iS).comp γ (rfl : q + c = q + c))) (zero_add _) := by
      intro y'
      rw [stratumGysinClass, Stacks.ExtFunctorial.mapExactFunctor_comp_functor uS ιS G q y',
        ← Ext.comp_assoc_of_second_deg_zero,
        ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor e.inv G q y',
        Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega),
        ← Stacks.ExtFunctorial.mapExactFunctor_comp_functor iS jS G q y',
        Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
        Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero]
    have hfun : ((fun y : Ext (uS.obj G) (uS.obj (unitSheaf (X := T) ℓ)) q =>
        (y.mapExactFunctor ιS).comp (stratumGysinClass i u j ι sq D γ) (rfl : q + c = q + c)) ∘
          ⇑(uS.mapExtAddHom G (unitSheaf (X := T) ℓ) q)) =
        (fun y => (Ext.mk₀ (e.inv.app G)).comp y (zero_add _)) ∘
          ⇑(Stacks.ExtAdjunction.extMap adjJ (iS.obj G) D (q + c)) ∘
          (fun y' : Ext G (unitSheaf (X := T) ℓ) q =>
            (y'.mapExactFunctor iS).comp γ (rfl : q + c = q + c)) := by
      funext y'
      exact key y'
    rw [hfun]
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).comp
      ((Stacks.ExtAdjunction.extMap_bijective adjJ (iS.obj G) D (q + c)).comp (hpur q))
  · intro q hq
    have := hvan q hq
    refine Function.Injective.subsingleton
      (f := fun x => (Ext.mk₀ (unitSheafInverseImageIsoOfClosed ι).inv).comp
        (Stacks.ExtAdjunction.extMap adj (unitSheaf (X := X) ℓ) (uS.obj G) q x) (zero_add q)) ?_
    exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).1.comp
      (Stacks.ExtAdjunction.extMap_bijective adj _ _ q).1
  · intro q hq
    have := hpur₀ q hq
    exact Function.Surjective.subsingleton
      (f := ⇑((Ext.mk₀ (e.inv.app G)).precomp D (zero_add q)) ∘
        ⇑(Stacks.ExtAdjunction.extMap (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j)
          (iS.obj G) D q))
      ((Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ _).2.comp
        (Stacks.ExtAdjunction.extMap_bijective
          (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j) (iS.obj G) D q).2)

omit [IsClosedImmersion i] in
/-- **`Ext` at coefficients supported on a stratum vanishes where it does on the stratum.** Given
a purity class `γ` for `G`, `Ext^{m+c}_X̄(j_! i_* G, D) = Ext^{m+c}_W(i_* G, j^{-1} D) ≅
Ext^m_T(G, Λ_T) = Ext^m_{T̄}(u_! G, u_! Λ_T)`, so it vanishes when the last group does. -/
theorem subsingleton_ext_stratum (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (hpur : ∀ q, Function.Bijective (fun y : Ext G (unitSheaf (X := T) ℓ) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) i)).comp γ
        (rfl : q + c = q + c)))
    (m : ℕ) (h : Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj G)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) u).obj (unitSheaf (X := T) ℓ)) m)) :
    Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).obj
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G)) D (m + c)) := by
  have h₁ : Subsingleton (Ext G (unitSheaf (X := T) ℓ) m) :=
    Function.Injective.subsingleton (Stacks.ExtAdjunction.mapExtAddHom_bijective
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) u) G (unitSheaf (X := T) ℓ) m).1
  have h₂ := Function.Surjective.subsingleton (hpur m).2
  exact Function.Surjective.subsingleton (Stacks.ExtAdjunction.extMap_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j)
    ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj G) D (m + c)).2

end Stacks.EtaleCohomology
