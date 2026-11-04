module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCompLocal

/-!
# From the affine opens to the whole square

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` quasi-compact and quasi-separated, `K ∈ D(𝒪_X)`,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`.  The composition `Lg^*Rf_*K ⟶ Rf'_*K'` is invertible as
soon as, for all affine opens `V ⊆ S`, `V' ⊆ g^{-1}(V)` and every affine open `U ⊆ f^{-1}(V)`,
the composition over every representative of `U` above `V' ⟶ V` is: the base is localized, and
the induction principle of Stacks 08DR runs over the quasi-compact opens of `f^{-1}(V)`.

## Main results

* `Stacks.Cohomology.BaseChangeCover.isIso_comp_of_affineOpens`.

## References

* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChangeCover

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The composition is invertible as soon as it is over every representative of every affine
open above a pair of affine opens of the bases.** -/
theorem isIso_comp_of_affineOpens (sq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toSheafedSpace)))
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (hbase : ∀ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V → IsAffineOpen V' →
      ∀ hle : V' ≤ g ⁻¹ᵁ V, ∀ U : X.Opens, IsAffineOpen U → U ≤ f ⁻¹ᵁ V →
        repGood% f f' g' V.ι V'.ι (g.resLE V V' hle) K K' φ U) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w) K ≫
      (derivedPushforward f'.toLRSHom.toShHom).map φ) := by
  refine isIso_comp_of_affineCharts sq K K' φ fun V V' hV hV' hle => ?_
  have : IsAffine V.toScheme := hV
  have hr : f ⁻¹ᵁ V.ι.opensRange = f ⁻¹ᵁ V := by rw [Scheme.Opens.opensRange_ι]
  have hgood := repGood_of_affineOpens (f := f) (f' := f') (g' := g') (iT := V.ι) (iT' := V'.ι)
    (gT := g.resLE V V' hle) (K := K) (K' := K') (φ := φ)
    (fun U hU hle' => hbase V V' hV hV' hle U hU (hle'.trans_eq hr))
  rw [hr] at hgood
  exact hgood

end Stacks.Cohomology.BaseChangeCover
