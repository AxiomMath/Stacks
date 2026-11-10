module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.Tower
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.Transport

/-!
# The fibrewise properties of an affine-space bundle, by induction on the rank

Let `(S, δ)` be the base situation of chapter 42. This file reduces the two fibrewise properties
`Stacks.Chow.FibreBoundaryLift` and `Stacks.Chow.FibreUnitDescent` of an affine-space bundle of
rank `r` to those of the projection of affine space `𝔸^r_T ⟶ T` over every base `T` (the
properties are local on the target, `Stacks.Chow.fibreBoundaryLift_of_openSquare`), and those in
turn, for rank `r + 1`, to the ranks `r` and `1` through the tower `𝔸^{r+1}_T = 𝔸^r_{𝔸^1_T}`
(`Stacks.Chow.affineSpaceSuccIso`, `Stacks.Chow.fibreBoundaryLift_comp`).

## Main definitions

* `Stacks.Chow.HasFibreProperties` — both fibrewise properties hold for a morphism at every
  point and in every degree.

## Main results

* `Stacks.Chow.hasFibreProperties_of_isAffineSpaceBundle_of_affineSpaceOver` — from the
  projection of affine space to every affine-space bundle of the same rank.
* `Stacks.Chow.hasFibreProperties_affineSpaceOver_succ` — the tower step.

## References

* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u})

/-- **Both fibrewise properties, everywhere.** The morphism `f : X ⟶ Y` over the base has the
boundary-lifting and the unit-descent properties, with fibre dimension `r`, at every point of
`Y` and in every degree. -/
def HasFibreProperties {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    (f : X ⟶ Y) (r : ℕ) : Prop :=
  ∀ (k : ℤ) (y : Y), FibreBoundaryLift C sX sY f r k y ∧ FibreUnitDescent C sX sY f r k y

attribute [local instance] flat_affineSpaceOver

/-- Both fibrewise properties pass along a square of open immersions. -/
private theorem fibreProperties_of_openSquare {X Y X' Y' : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) (f : X ⟶ Y) (f' : X' ⟶ Y') (jX : X' ⟶ X)
    [IsOpenImmersion jX] (jY : Y' ⟶ Y) [IsOpenImmersion jY] {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY'] (hsq : jX ≫ f = f' ≫ jY)
    (hpre : f.base ⁻¹' Set.range jY.base ⊆ Set.range jX.base) (hX : jX ≫ sX = sX')
    (hY : jY ≫ sY = sY') (r : ℕ) (k : ℤ) (y' : Y')
    (h : FibreBoundaryLift C sX' sY' f' r k y' ∧ FibreUnitDescent C sX' sY' f' r k y') :
    FibreBoundaryLift C sX sY f r k (jY.base y') ∧ FibreUnitDescent C sX sY f r k (jY.base y') :=
  ⟨fibreBoundaryLift_of_openSquare C sX sY f f' jX jY hsq hpre hX hY r k y' h.1,
    fibreUnitDescent_of_openSquare C sX sY f f' jX jY hsq hpre hX hY r k y' h.2⟩

/-- **From the projection of affine space to every affine-space bundle of the same rank.** The
fibrewise properties at a point `y` are transported from a trivialization over an open
neighbourhood of `y`. -/
theorem hasFibreProperties_of_isAffineSpaceBundle_of_affineSpaceOver (r : ℕ)
    (htriv : ∀ (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT],
      HasFibreProperties C ((𝔸(ULift.{u} (Fin r); T) ↘ T) ≫ sT) sT
        (𝔸(ULift.{u} (Fin r); T) ↘ T) r)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (hbase : f ≫ sY = sX) (hb : IsAffineSpaceBundle f r) :
    HasFibreProperties C sX sY f r := by
  intro k y
  obtain ⟨V, hyV, e, he⟩ := hb y
  let jX : 𝔸(ULift.{u} (Fin r); V.toScheme) ⟶ X := e.inv ≫ (f ⁻¹ᵁ V).ι
  have hsq : jX ≫ f = (𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) ≫ V.ι := by
    simp only [jX, Category.assoc, ← morphismRestrict_ι, ← he]
    simp
  have hpre : f.base ⁻¹' Set.range V.ι.base ⊆ Set.range jX.base := by
    intro x hx
    rw [Set.mem_preimage, Scheme.Opens.range_ι] at hx
    refine ⟨e.hom ⟨x, hx⟩, ?_⟩
    change (e.hom ≫ e.inv ≫ (f ⁻¹ᵁ V).ι) ⟨x, hx⟩ = x
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hX : jX ≫ sX = (𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) ≫ (V.ι ≫ sY) := by
    rw [← hbase, ← Category.assoc, hsq, Category.assoc]
  have : LocallyOfFiniteType (V.ι ≫ sY) := inferInstance
  have h := htriv V.toScheme (V.ι ≫ sY) k ⟨y, hyV⟩
  exact fibreProperties_of_openSquare C sX sY f _ jX V.ι hsq hpre hX rfl r k ⟨y, hyV⟩ h

/-- **The tower step.** If the projections of affine space of ranks `r` and `1` have the
fibrewise properties over every base, and the local rings of the closure of the generic point of
a fibre of the affine line at the other points of that fibre are discrete valuation rings, then
the projection of affine space of rank `r + 1` has the fibrewise properties over every base:
`𝔸^{r+1}_T = 𝔸^r_{𝔸^1_T}`. -/
theorem hasFibreProperties_affineSpaceOver_succ (r : ℕ)
    (hr : ∀ (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT],
      HasFibreProperties C ((𝔸(ULift.{u} (Fin r); T) ↘ T) ≫ sT) sT
        (𝔸(ULift.{u} (Fin r); T) ↘ T) r)
    (h1 : ∀ (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT],
      HasFibreProperties C ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) sT
        (𝔸(ULift.{u} (Fin 1); T) ↘ T) 1)
    (hdvr : ∀ (T : Scheme.{u}) (ζ w : 𝔸(ULift.{u} (Fin 1); T)) (hw : ζ ⤳ w),
      (𝔸(ULift.{u} (Fin 1); T) ↘ T).base ζ = (𝔸(ULift.{u} (Fin 1); T) ↘ T).base w → ζ ≠ w →
        IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
          (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT] :
    HasFibreProperties C ((𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT) sT
      (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) (r + 1) := by
  intro k x
  set p := 𝔸(ULift.{u} (Fin 1); T) ↘ T
  set q := 𝔸(ULift.{u} (Fin r); 𝔸(ULift.{u} (Fin 1); T)) ↘ 𝔸(ULift.{u} (Fin 1); T)
  have hbq : IsAffineSpaceBundle q r := isAffineSpaceBundle_affineSpaceOver _ r
  have hbp : IsAffineSpaceBundle p 1 := isAffineSpaceBundle_affineSpaceOver _ 1
  have hL := fibreBoundaryLift_comp C (q ≫ p ≫ sT) (p ≫ sT) sT q p rfl rfl hbq hbp
    (fun k z ↦ (hr _ (p ≫ sT) k z).1) (fun k z ↦ (hr _ (p ≫ sT) k z).2)
    (fun k x ↦ (h1 T sT k x).1) (hdvr T) k x
  have hU := fibreUnitDescent_comp C (q ≫ p ≫ sT) (p ≫ sT) sT q p rfl rfl hbq hbp
    (fun k z ↦ (hr _ (p ≫ sT) k z).2) (fun k x ↦ (h1 T sT k x).2) k x
  -- transport along the isomorphism `𝔸^r_{𝔸^1_T} ≅ 𝔸^{r+1}_T`
  have hsq : (affineSpaceSuccIso T r).inv ≫ (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) =
      (q ≫ p) ≫ 𝟙 T := by
    rw [← affineSpaceSuccIso_hom_over T r, Iso.inv_hom_id_assoc, Category.comp_id]
  have hpre : (𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T).base ⁻¹' Set.range (𝟙 T : T ⟶ T).base ⊆
      Set.range (affineSpaceSuccIso T r).inv.base := fun z _ ↦
    ⟨(affineSpaceSuccIso T r).hom z, by
      change ((affineSpaceSuccIso T r).hom ≫ (affineSpaceSuccIso T r).inv) z = z
      rw [Iso.hom_inv_id]
      rfl⟩
  have hX : (affineSpaceSuccIso T r).inv ≫ ((𝔸(ULift.{u} (Fin (r + 1)); T) ↘ T) ≫ sT) =
      q ≫ p ≫ sT := by
    rw [← Category.assoc, hsq, Category.comp_id, Category.assoc]
  exact fibreProperties_of_openSquare C _ sT _ (q ≫ p) _ (𝟙 T) hsq hpre hX
    (Category.id_comp sT) (r + 1) k x ⟨hL, hU⟩

/-- **All positive ranks from rank one.** If the projection of the affine line has the fibrewise
properties over every base, and the local rings of the closure of the generic point of a fibre of
the affine line at the other points of that fibre are discrete valuation rings, then the
projection of affine space of every positive rank has the fibrewise properties over every
base. -/
theorem hasFibreProperties_affineSpaceOver_of_affineLine
    (h1 : ∀ (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT],
      HasFibreProperties C ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) sT
        (𝔸(ULift.{u} (Fin 1); T) ↘ T) 1)
    (hdvr : ∀ (T : Scheme.{u}) (ζ w : 𝔸(ULift.{u} (Fin 1); T)) (hw : ζ ⤳ w),
      (𝔸(ULift.{u} (Fin 1); T) ↘ T).base ζ = (𝔸(ULift.{u} (Fin 1); T) ↘ T).base w → ζ ≠ w →
        IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
          (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    (r : ℕ) (hr : 1 ≤ r) (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT] :
    HasFibreProperties C ((𝔸(ULift.{u} (Fin r); T) ↘ T) ≫ sT) sT
      (𝔸(ULift.{u} (Fin r); T) ↘ T) r := by
  induction r, hr using Nat.le_induction generalizing T with
  | base => exact h1 T sT
  | succ r _ ih =>
    exact hasFibreProperties_affineSpaceOver_succ C r (fun T sT _ ↦ ih T sT) h1 hdvr T sT

/-- **Injectivity of flat pullback along an affine-space bundle of positive rank, from the affine
line.** -/
theorem flatPullbackChow_injective_of_isAffineSpaceBundle_of_affineLine
    (h1 : ∀ (T : Scheme.{u}) (sT : T ⟶ C.S) [LocallyOfFiniteType sT],
      HasFibreProperties C ((𝔸(ULift.{u} (Fin 1); T) ↘ T) ≫ sT) sT
        (𝔸(ULift.{u} (Fin 1); T) ↘ T) 1)
    (hdvr : ∀ (T : Scheme.{u}) (ζ w : 𝔸(ULift.{u} (Fin 1); T)) (hw : ζ ⤳ w),
      (𝔸(ULift.{u} (Fin 1); T) ↘ T).base ζ = (𝔸(ULift.{u} (Fin 1); T) ↘ T).base w → ζ ≠ w →
        IsDiscreteValuationRing ((integralComponentAt ζ).subscheme.presheaf.stalk
          (pointClosurePoint ζ (specializes_iff_mem_closure.mp hw))))
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f]
    (hbase : f ≫ sY = sX) (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hb : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Injective (flatPullbackChowOfRelativeDimension C sX sY f hbase r hf k) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact (flatPullbackChow_bijective_of_isAffineSpaceBundle_zero C sX sY f hbase hf hb k _).1
  have hP := hasFibreProperties_of_isAffineSpaceBundle_of_affineSpaceOver C r
    (fun T sT _ ↦ hasFibreProperties_affineSpaceOver_of_affineLine C h1 hdvr r hr T sT)
    sX sY f hbase hb
  exact flatPullbackChow_injective_of_fibreProperties C sX sY f hbase hb hf k
    (fun y ↦ (hP (k + r) y).1) (fun y ↦ (hP (k + r) y).2)
    (pointwiseDivisorDifferential_bundleChainPullback C sX sY f hbase hb k)

end Stacks.Chow

end
