module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.ChartFlatness
public import StacksFrontier.AlgebraicGeometry.BaseChange.TensorFlatPushforwardBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived pushforward of a derived tensor product with a complex flat over
the base

Let `f : X ⟶ S` be quasi-compact and quasi-separated, `E ∈ D_QCoh(𝒪_X)` and `𝒢^•` a bounded above
complex of quasi-coherent `𝒪_X`-modules flat over `S`. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical map `Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_isPullback`: **Stacks 0A1D**.

## Implementation notes

The proof replaces `E` by a K-flat complex `P` and identifies the map with the composition
`Lg^*Rf_*Tot(P ⊗ 𝒢) ⟶ Rf'_*(g')^*Tot(P ⊗ 𝒢)`, which is checked on the Cartesian affine-open
charts: there `P` becomes `M̃` for a K-flat complex `M` of modules over `A = 𝒪_X(U)`, `𝒢` becomes
`Ñ` for the complex `N` of its sections, which is a bounded above complex of flat modules over
`R = 𝒪_S(V)`, and `M ⊗_A N` is K-flat over `R`, so that derived and degreewise base change of
`(M ⊗_A N)~` agree.

## References

* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0A1D.** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes,
`E` an object of `D_QCoh(𝒪_X)` and `𝒢^•` a bounded above complex of quasi-coherent
`𝒪_X`-modules flat over `S`. For every cartesian square the canonical map

`Lg^*Rf_*(E ⊗^L_{𝒪_X} 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L_{𝒪_{X'}} (g')^*𝒢^•)`

of `tensorFlatBaseChangeMap`, with the ordinary pullback of `𝒢^•` on the right, is an
isomorphism. -/
@[stacks 0A1D]
theorem isIso_tensorFlatBaseChangeMap_of_isPullback {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (G : CochainComplex X.Modules ℤ)
    (hGminus : CochainComplex.minus X.Modules G)
    (hGqcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X n)) :
    IsIso (tensorFlatBaseChangeMap f g f' g' sq E G) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso E
  have hPq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj P)).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e.symm) (hE n)
  have key := isIso_derivedBaseChangeComp_totalTensor_of_charts hsq P G hP hPq hGqcoh
    fun U V hU hV hUV => kFlat_sectionsComplex_pullback_fromSpec f hU hV hUV G hGminus hGqcoh
      hGflat
  have k₂ := (isIso_derivedBaseChangeComp_tensor_iff_of_kFlat f g f' g' hsq.w P G hP).2 key
  exact (isIso_derivedBaseChangeComp_tensor_iff_of_iso f g f' g' sq e _ _ _).1 k₂

end AlgebraicGeometry
