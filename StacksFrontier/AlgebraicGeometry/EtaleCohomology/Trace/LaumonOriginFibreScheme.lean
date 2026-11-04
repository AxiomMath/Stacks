module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonSpecializationInjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFamilyStalkPurity
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The fibres of Laumon's family are base changes of the curve

Let `k → k'` be a field extension, `U ≅ 𝔸¹_k` (by `e`) and
`pr₂ : 𝔸² = Spec k'[x][t] → W = Spec k'[t]` the second projection of Laumon's family
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). The ring square `k → k[x]`, `k → k'[t]`,
`k'[x][t]` is a pushout (paste the polynomial base changes `k[x] ⊗_k k' = k'[x]` and
`k'[x] ⊗_{k'} k'[t] = k'[x][t]`), so `𝔸²` is `W ×_k U` through `pr₂` and `x ↦ x`. Pasting with a
fibre square of `pr₂` over a point `y` of `W` identifies any fibre `Y` with `U ×_k κ(y)`, over
`κ(y)` and over `U`; the `k`-algebra structure of `κ(y)` is `k → k'[t] → κ(y)`
(`laumonPointAlgebra`).

All names are in the namespace `Stacks.EtaleCohomology`.

## Main results

* `isPushout_C_mapRingHom_C`: `k'[x][t] = k'[x] ⊗_{k'} k'[t]`, a pushout of commutative rings.
* `isPushout_C_mapRingHom`: `k'[x] = k[x] ⊗_k k'`, a pushout of commutative rings.
* `isPullback_laumonPlane`: `𝔸²_{k'} = 𝔸¹_{k',t} ×_k 𝔸¹_{k,x}`.
* `isPullback_laumonPlane_curve`: `𝔸²_{k'} = 𝔸¹_{k',t} ×_k U` for `e : U ≅ 𝔸¹_k`.
* `isPullback_laumonFibre_curve`: a fibre of `pr₂` over a point `y` of `W` is `U ×_k κ(y)`.

## Implementation notes

All ring maps are written explicitly (`Polynomial.C`, `Polynomial.mapRingHom`): the two
`Polynomial k'`-algebra structures on `Polynomial (Polynomial k')` are never used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace Stacks.EtaleCohomology

section Rings

/-- **`k'[x][t] = k'[x] ⊗_{k'} k'[t]`**: the square of `C : k' → k'[x]`, `C : k' → k'[t]`,
`C : k'[x] → k'[x][t]` and `map C : k'[t] → k'[x][t]` is a pushout of commutative rings. -/
public theorem isPushout_C_mapRingHom_C (k' : Type u) [CommRing k'] :
    IsPushout (CommRingCat.ofHom (C : k' →+* Polynomial k'))
      (CommRingCat.ofHom (C : k' →+* Polynomial k'))
      (CommRingCat.ofHom (C : Polynomial k' →+* Polynomial (Polynomial k')))
      (CommRingCat.ofHom (mapRingHom (C : k' →+* Polynomial k'))) := by
  let iA : Algebra (Polynomial k') (Polynomial (Polynomial k')) :=
    Polynomial.algebra k' (Polynomial k')
  let iS : Algebra (Polynomial k') (Polynomial (Polynomial k')) := Polynomial.algebraOfAlgebra
  have hA : @IsScalarTower k' (Polynomial k') (Polynomial (Polynomial k')) _
      (@Algebra.toSMul _ _ _ _ iA) _ := by
    refine @IsScalarTower.of_algebraMap_eq k' (Polynomial k') (Polynomial (Polynomial k')) _ _ _ _
      iA _ fun r => ?_
    show C (C r) = mapRingHom C (C r)
    simp
  have hS : @IsScalarTower k' (Polynomial k') (Polynomial (Polynomial k')) _
      (@Algebra.toSMul _ _ _ _ iS) _ := by
    refine @IsScalarTower.of_algebraMap_eq k' (Polynomial k') (Polynomial (Polynomial k')) _ _ _ _
      iS _ fun r => ?_
    rfl
  have hP : @Algebra.IsPushout k' (Polynomial k') _ _ _ (Polynomial k')
      (Polynomial (Polynomial k')) _ _ _ iS iA _ hA hS := inferInstance
  exact @CommRingCat.isPushout_of_isPushout k' (Polynomial k') (Polynomial k')
    (Polynomial (Polynomial k')) _ _ _ _ _ iS _ iA _ hA hS hP

/-- **`k'[x] = k[x] ⊗_k k'`**: the square of `algebraMap : k → k'`, `C : k → k[x]`,
`C : k' → k'[x]` and `map : k[x] → k'[x]` is a pushout of commutative rings. -/
public theorem isPushout_C_mapRingHom (k k' : Type u) [CommRing k] [CommRing k'] [Algebra k k'] :
    IsPushout (CommRingCat.ofHom (algebraMap k k')) (CommRingCat.ofHom (C : k →+* Polynomial k))
      (CommRingCat.ofHom (C : k' →+* Polynomial k'))
      (CommRingCat.ofHom (mapRingHom (algebraMap k k'))) := by
  let iA : Algebra (Polynomial k) (Polynomial k') := Polynomial.algebra k k'
  have hA : IsScalarTower k (Polynomial k) (Polynomial k') :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show C (algebraMap k k' r) = mapRingHom (algebraMap k k') (C r)
      simp
  exact CommRingCat.isPushout_of_isPushout k k' (Polynomial k) (Polynomial k')

end Rings

section Schemes

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k']

/-- **`𝔸²_{k'} = 𝔸¹_{k',t} ×_k 𝔸¹_{k,x}`**: `Spec k'[x][t]` with `pr₂` (`t ↦ t`) and
`x ↦ x` is the fibre product of the `t`-line over `k'` and the `x`-line over `k`. -/
public theorem isPullback_laumonPlane :
    IsPullback (Spec.map (CommRingCat.ofHom (mapRingHom (C : k' →+* Polynomial k'))))
      (Spec.map (CommRingCat.ofHom (C : Polynomial k' →+* Polynomial (Polynomial k'))) ≫
        Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k'))))
      (Spec.map (CommRingCat.ofHom (C : k' →+* Polynomial k')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k')))
      (Spec.map (CommRingCat.ofHom (C : k →+* Polynomial k))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom_C k')).flip.paste_vert
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom k k'))

/-- **`𝔸²_{k'} = 𝔸¹_{k',t} ×_k U`** for `e : U ≅ 𝔸¹_k` over `k`. -/
public theorem isPullback_laumonPlane_curve {U : Scheme.{u}} (f : U ⟶ Spec (.of k))
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f) :
    IsPullback ((Spec.map (CommRingCat.ofHom (C : Polynomial k' →+* Polynomial (Polynomial k'))) ≫
        Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k')))) ≫ inv e)
      (Spec.map (CommRingCat.ofHom (mapRingHom (C : k' →+* Polynomial k')))) f
      (Spec.map (CommRingCat.ofHom (C : k' →+* Polynomial k')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k'))) := by
  have t : IsPullback (inv e) (Spec.map (CommRingCat.ofHom (C : k →+* Polynomial k))) f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← he, IsIso.inv_hom_id_assoc, Category.comp_id, Polynomial.algebraMap_eq]⟩
  have h := (isPullback_laumonPlane k k').flip.paste_horiz t
  rwa [Category.comp_id] at h

variable {B : BigEtaleSite.{u}} {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))}

/-- **Evaluation at a point of the `t`-line**: `Spec κ(y) → Spec k'[t] → Spec A` is the spectrum
of `A → k'[t] → κ(y)` (`Stacks.EtaleCohomology.laumonPointRingHom`). -/
public theorem fromSpecResidueField_comp_SpecMap_laumonPointRingHom
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) {A : CommRingCat.{u}}
    (ψ : A ⟶ CommRingCat.of (Polynomial k')) :
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y ≫ Spec.map ψ =
      Spec.map (ψ ≫ CommRingCat.ofHom (laumonPointRingHom (𝟙 _) y)) := by
  have h₁ := Scheme.fromSpecResidueField_toSpecΓ
    (X := (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) y
  have h₂ := toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of (Polynomial k'))
  have h₃ : ψ ≫ CommRingCat.ofHom (laumonPointRingHom (𝟙 _) y) =
      ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv ≫
        (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.Γevaluation y := by
    ext a
    simp [laumonPointRingHom]
  calc _ = (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y ≫
        ((Spec (CommRingCat.of (Polynomial k'))).toSpecΓ ≫
          Spec.map (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv) ≫ Spec.map ψ := by
        rw [h₂, Category.id_comp]
    _ = _ := by
        rw [← Category.assoc, ← Category.assoc, h₁, h₃, Spec.map_comp, Spec.map_comp,
          Category.assoc]

variable {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))}

/-- **A fibre of `pr₂` over a point `y` of the `t`-line is `U ×_k κ(y)`**: pasting the fibre
square with `𝔸²_{k'} = 𝔸¹_{k',t} ×_k U`, the fibre `Y` with `Y → 𝔸² → U` (`x ↦ x`) and
`Y → Spec κ(y)` is the fibre product of `f : U → Spec k` and `Spec κ(y) → Spec k`, the latter
being the spectrum of `k → k'[t] → κ(y)`. -/
public theorem isPullback_laumonFibre_curve {U : Scheme.{u}} (f : U ⟶ Spec (.of k))
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) {Y : B.Scheme}
    (i : Y ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    (fY : Y.1 ⟶
      Spec (.of ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y)) :
    IsPullback (B.inclusion.map i ≫
        (Spec.map (CommRingCat.ofHom (C : Polynomial k' →+* Polynomial (Polynomial k'))) ≫
          Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k k')))) ≫ inv e) fY f
      (Spec.map (CommRingCat.ofHom
        ((laumonPointRingHom (𝟙 _) y).comp (algebraMap k (Polynomial k'))))) := by
  have h := hY.paste_horiz (isPullback_laumonPlane_curve k k' f e he)
  have hb : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y ≫
      Spec.map (CommRingCat.ofHom (C : k' →+* Polynomial k')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k')) =
      Spec.map (CommRingCat.ofHom
        ((laumonPointRingHom (𝟙 _) y).comp (algebraMap k (Polynomial k')))) := by
    rw [← Spec.map_comp, fromSpecResidueField_comp_SpecMap_laumonPointRingHom]
    rfl
  rwa [hb] at h

end Schemes

end Stacks.EtaleCohomology

end
