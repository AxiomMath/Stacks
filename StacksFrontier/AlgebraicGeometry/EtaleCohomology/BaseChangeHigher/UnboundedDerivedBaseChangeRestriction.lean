module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus

/-!
# An unbounded derived base change map restricts to the bounded below one

Let `F : A ⥤ B` and `F' : C ⥤ D` be additive functors (direct images), `G : B ⥤ D` and
`G' : A ⥤ C` exact functors (inverse images), and `τ : F ⋙ G ⟶ G' ⋙ F'` a comparison (an
underived base change map). Two derived base change maps are built from `τ`:

* on bounded below derived categories, `Stacks.Cohomology.BaseChange.derived`, the descent of `τ`
  along the derived-functor unit of `RF⁺ ⋙ RG⁺`;
* on unbounded derived categories, any `bc : RF ⋙ G ⟶ G' ⋙ RF'`, for unbounded right derived
  functors `RF` and `RF'`, satisfying the factorisation `UnboundedFac`: precomposed with the unit
  of `RF` it is `τ` followed by the unit of `RF'`. For the étale direct and inverse images this
  is `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac`.

**This file proves that the two agree on `D⁺(A)`**, under the identifications
`CategoryTheory.Functor.boundedDerivedIso` of `RF` and `RF'` on bounded below objects with `RF⁺`
and `RF'⁺`, and `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso` of the right derived
functors of the exact functors with their degreewise actions.

## Main definitions

* `Stacks.Cohomology.BaseChange.UnboundedFac` — the factorisation that pins an unbounded base
  change map.

## Main results

* `Stacks.Cohomology.BaseChange.unboundedFac_of_homotopy` — `UnboundedFac` from a factorisation
  through `τ` conjugated by the identity comparisons on homotopy categories.
* `Stacks.Cohomology.BaseChange.ι_map_derived_app_of_unboundedFac` — the bounded below base
  change map, read in `D(D)` through the identifications, is the unbounded one.

## Implementation notes

Both sides are transformations out of `RF⁺ ⋙ G⁺ ⋙ ι`, which is a right derived functor of
degreewise `F` followed by `G⁺ ⋙ ι` (its unit is invertible on bounded below complexes of
injectives). By the uniqueness of transformations out of a right derived functor
(`CategoryTheory.Functor.rightDerived_ext`) it suffices to compare them after that unit, at an
arbitrary bounded below complex; there each side collapses, by its own factorisation, to `τ`
followed by the unit of `RF'`. The rearrangement is `unbounded_chase`, at variables.

## References

* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedBaseChangePlus
  (mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient_obj)

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Chase

variable {𝒞 : Type*} [Category* 𝒞]

/-- The rearrangement behind `ι_map_derived_app_of_unboundedFac`, at variables of an abstract
category. The hypotheses are, in order: naturality of the comparison of the exact functor `G`,
its value on the image of the localization, the factorisation of the bounded below base change
map, the cancellation of the unit of `RG⁺`, naturality of the crossing for `F'`, the pinning of
that crossing, the value of the comparison for `G'`, the factorisation of the unbounded base
change map, the cancellation of the factorisation of `G`, and the pinning of the crossing for
`F`. -/
theorem unbounded_chase {P0 P1 P2 P3 P4 P5 P0' Q0 Q1 Q2 Q3 R1 : 𝒞}
    {gu : P0 ⟶ P1} {a1 : P1 ⟶ P2} {a2 : P2 ⟶ P3} {a3 : P3 ⟶ P4} {a4 : P4 ⟶ P5}
    {b1 : P0 ⟶ P0'} {ru : P0' ⟶ P2} (n1 : gu ≫ a1 = b1 ≫ ru)
    {fG : P0 ⟶ Q0} {uGM : Q0 ⟶ P0'} (n2 : b1 = fG ≫ uGM)
    {iuGM : P0' ⟶ Q0} {tq : Q0 ⟶ Q1} {uFp : Q1 ⟶ Q2} {rup : Q2 ⟶ P3}
    (f1 : ru ≫ a2 = iuGM ≫ tq ≫ uFp ≫ rup) (hinv : uGM ≫ iuGM = 𝟙 Q0)
    {bN : Q2 ⟶ Q3} {rfu : Q3 ⟶ P4} (n3 : rup ≫ a3 = bN ≫ rfu)
    {uFN : Q1 ⟶ Q3} (p1 : uFp ≫ bN = uFN)
    {rfac : Q3 ⟶ P5} (n4 : rfu ≫ a4 = rfac)
    {fGinv : Q0 ⟶ P0} {gdu : P0 ⟶ R1} {bcK : R1 ⟶ P5}
    (hbc : fGinv ≫ gdu ≫ bcK = tq ≫ uFN ≫ rfac) (hfG : fG ≫ fGinv = 𝟙 P0)
    {gb : P1 ⟶ R1} (p2 : gu ≫ gb = gdu) :
    gu ≫ a1 ≫ a2 ≫ a3 ≫ a4 = gu ≫ gb ≫ bcK := by
  rw [reassoc_of% n1, n2, Category.assoc, reassoc_of% f1, reassoc_of% hinv, reassoc_of% n3,
    reassoc_of% p1, n4, ← hbc, reassoc_of% hfG, reassoc_of% p2]

end Chase

section Comparison

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  (τ : F ⋙ G ⟶ G' ⋙ F')
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (uF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (RF' : DerivedCategory C ⥤ DerivedCategory D)
  (uF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  (bc : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF')

/-- **The factorisation that pins an unbounded base change map** `bc : RF ⋙ G ⟶ G' ⋙ RF'`: at
every complex `K`, precomposed with the factorisation of `G` and with `G` of the unit of `RF`, it
is `τ` applied degreewise, followed by the unit of `RF'` and `RF'` of the factorisation of `G'`.
A named proposition, so that a hypothesis of this shape is compared argument by argument. -/
def UnboundedFac : Prop :=
  ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
    G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (uF.app K) ≫ bc.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) ≫
        uF'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RF'.map (G'.mapDerivedCategoryFactorsh.inv.app K)

omit [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] in
/-- **`UnboundedFac` from a factorisation through a degreewise comparison on homotopy categories**
which is `τ` conjugated by the identity comparisons `Functor.mapHomotopyCategoryCompIso`, the
shape in which `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` is stated. Proving
`UnboundedFac` through this lemma keeps the components of `NatTrans.mapHomotopyCategory τ` at
the abstract spelling, where their comparison is free. -/
theorem unboundedFac_of_homotopy
    (τh : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F'.mapHomotopyCategory (ComplexShape.up ℤ))
    (hτh : τh = (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (G' ⋙ F')) (ComplexShape.up ℤ)).inv)
    (hfac : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map (uF.app K) ≫ bc.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map (τh.app K) ≫
          uF'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          RF'.map (G'.mapDerivedCategoryFactorsh.inv.app K)) :
    UnboundedFac F F' G G' τ RF uF RF' uF' bc := by
  intro K
  have h2 : τh.app K = (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [hτh, mapHomotopyCategoryCompIso_hom_comp_comp_inv_app_quotient_obj,
      NatTrans.mapHomotopyCategory_app]
    rfl
  rw [hfac K, h2]
  rfl

variable [RF.IsRightDerivedFunctor uF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor uF' (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (hresA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (hresC : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The bounded below base change map is the unbounded one on `D⁺`.** For `K` in `D⁺(A)`, the
bounded below derived base change map `derived F F' G G' τ` at `K`, read in `D(D)` between the
identification of `G` with its right derived functor at `RF⁺ K` and the identifications of `RF'`
with `RF'⁺` and of `G'` with its right derived functor, is `G` of the identification of `RF⁺ K`
with `RF K` followed by the unbounded base change map `bc` at `K`, as soon as `bc` satisfies the
factorisation `UnboundedFac`. -/
theorem ι_map_derived_app_of_unboundedFac (hbc : UnboundedFac F F' G G' τ RF uF RF' uF' bc)
    (K : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.map ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.app
        (F.rightDerivedFunctorPlus.obj K)) ≫
      DerivedCategory.Plus.ι.map
        ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnit)).app K) ≫
      (F'.boundedDerivedIso RF' uF' hresC).hom.app (G'.rightDerivedFunctorPlus.obj K) ≫
      RF'.map (DerivedCategory.Plus.ι.map
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv.app K)) =
    G.mapDerivedCategory.map ((F.boundedDerivedIso RF uF hresA).hom.app K) ≫
      bc.app (DerivedCategory.Plus.ι.obj K) := by
  let H₁ : DerivedCategory.Plus B ⥤ DerivedCategory D :=
    G.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι
  let α : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ H₁ ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ H₁) :=
    Functor.whiskerRight F.rightDerivedFunctorPlusUnit H₁ ≫ (Functor.associator _ _ _).hom
  have : (F.rightDerivedFunctorPlus ⋙ H₁).IsRightDerivedFunctor α
      (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso α
      (fun K ↦ by dsimp [α]; infer_instance)
  let L : F.rightDerivedFunctorPlus ⋙ H₁ ⟶
      DerivedCategory.Plus.ι ⋙ (G'.mapDerivedCategory ⋙ RF') :=
    Functor.whiskerLeft F.rightDerivedFunctorPlus
        (Functor.whiskerRight (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom
          DerivedCategory.Plus.ι) ≫
      Functor.whiskerRight (derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnit))
        DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft G'.rightDerivedFunctorPlus (F'.boundedDerivedIso RF' uF' hresC).hom ≫
      Functor.whiskerRight
        (Functor.whiskerRight (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv
          DerivedCategory.Plus.ι) RF'
  let R : F.rightDerivedFunctorPlus ⋙ H₁ ⟶
      DerivedCategory.Plus.ι ⋙ (G'.mapDerivedCategory ⋙ RF') :=
    Functor.whiskerRight (F.boundedDerivedIso RF uF hresA).hom G.mapDerivedCategory ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι bc
  have hLR : L = R := by
    refine Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ H₁) α
      (HomotopyCategory.Plus.quasiIso A) _ L R ?_
    ext Kh
    let M := F.mapHomotopyCategoryPlus.obj Kh
    let u := F.rightDerivedFunctorPlusUnit.app Kh
    let N := G'.mapHomotopyCategoryPlus.obj Kh
    have n1 : DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map u) ≫
        DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.app
            (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj Kh))) =
        DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.app
            (DerivedCategory.Plus.Qh.obj M)) ≫
          DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map u) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.naturality u)
    have n2 : DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G).hom.app
            (DerivedCategory.Plus.Qh.obj M)) =
        DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlusFactorsh.hom.app M) ≫
          DerivedCategory.Plus.ι.map ((asIso G.rightDerivedFunctorPlusUnit).hom.app M) := by
      rw [Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh, ← Functor.map_comp]
      rfl
    have f1 : DerivedCategory.Plus.ι.map (G.rightDerivedFunctorPlus.map u) ≫
        DerivedCategory.Plus.ι.map
          ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnit)).app
            (DerivedCategory.Plus.Qh.obj Kh)) =
        DerivedCategory.Plus.ι.map ((asIso G.rightDerivedFunctorPlusUnit).inv.app M) ≫
          DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh)) ≫
          DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnit.app N) ≫
          DerivedCategory.Plus.ι.map
            (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnit.app Kh)) := by
      rw [← Functor.map_comp, derived_fac_app, onHomotopy_app]
      rfl
    have hinv : DerivedCategory.Plus.ι.map ((asIso G.rightDerivedFunctorPlusUnit).hom.app M) ≫
        DerivedCategory.Plus.ι.map ((asIso G.rightDerivedFunctorPlusUnit).inv.app M) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    have n3 := (F'.boundedDerivedIso RF' uF' hresC).hom.naturality
      (G'.rightDerivedFunctorPlusUnit.app Kh)
    have p1 := Functor.boundedDerivedIso_hom_app F' RF' uF' hresC N
    have n4 : RF'.map (DerivedCategory.Plus.ι.map (G'.rightDerivedFunctorPlusUnit.app Kh)) ≫
        RF'.map (DerivedCategory.Plus.ι.map
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso G').inv.app
            (DerivedCategory.Plus.Qh.obj Kh))) =
        RF'.map (G'.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.Plus.ι A).obj Kh)) := by
      rw [← Functor.map_comp, ← Functor.map_comp,
        Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_inv_app_Qh]
      simp only [Iso.trans_inv, NatTrans.comp_app, asIso_inv, IsIso.hom_inv_id_assoc,
        NatIso.isIso_inv_app]
      congr 1
    have hfG := Iso.hom_inv_id_app G.mapDerivedCategoryFactorsh
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.Plus.ι A).obj Kh))
    have p2 : G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map u) ≫
        G.mapDerivedCategory.map ((F.boundedDerivedIso RF uF hresA).hom.app
          (DerivedCategory.Plus.Qh.obj Kh)) =
        G.mapDerivedCategory.map (uF.app ((HomotopyCategory.Plus.ι A).obj Kh)) := by
      rw [← Functor.map_comp, Functor.boundedDerivedIso_hom_app]
      rfl
    have key := unbounded_chase n1 n2 f1 hinv n3 p1 n4
      (hbc ((HomotopyCategory.Plus.ι A).obj Kh)) hfG p2
    change (H₁.map u ≫ 𝟙 _) ≫ L.app (DerivedCategory.Plus.Qh.obj Kh) =
      (H₁.map u ≫ 𝟙 _) ≫ R.app (DerivedCategory.Plus.Qh.obj Kh)
    rwa [Category.comp_id]
  exact NatTrans.congr_app hLR K

end Comparison

end Stacks.Cohomology.BaseChange

end
