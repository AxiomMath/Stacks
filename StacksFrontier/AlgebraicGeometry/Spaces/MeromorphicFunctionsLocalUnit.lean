module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsLocalFraction

/-!
# A meromorphic function which multiplies injectively is locally a unit

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `x` be
a section of the sheaf `𝒦_F` of meromorphic functions (Stacks 0EN3) over an étale scheme chart
`U`.  Suppose multiplication by `x` is injective on the meromorphic functions over every chart
over `U`.  Then `x` is a unit on a covering sieve of `U`: there `x` is a fraction `b/c` of
sections of `𝒪_F` with `c` regular (Stacks 0EMC), and `b = x · c` is then regular as well.

## Main results

* `AlgebraicGeometry.Space.toMeromorphicFunctionSheaf_app_apply_eq_toSheafify`: the canonical map
  `𝒪_F(Z) ⟶ 𝒦_F(Z)` is the sectionwise localization followed by the sheafification map.
* `AlgebraicGeometry.Space.exists_sieve_isUnit_of_injective_mul`: a meromorphic function whose
  multiplication is injective over every chart over `U` is a unit on a covering sieve of `U`.

## References

* [Stacks Project, Tag 0EN3](https://stacks.math.columbia.edu/tag/0EN3)
* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The canonical map `𝒪_F(Z) ⟶ 𝒦_F(Z)` is the localization map of Stacks 0EMC followed by the
sheafification map, on sections over a chart. -/
theorem toMeromorphicFunctionSheaf_app_apply_eq_toSheafify (Z : SmallEtale B S hS F)
    (z : (structurePresheaf B S hS F).obj (op Z)) :
    ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom z =
      ((toSheafify (SmallEtale.topology B S hS F)
          (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf).app (op Z)).hom
        (algebraMap ((structurePresheaf B S hS F).obj (op Z))
          ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.obj (op Z)) z) :=
  congrArg (fun φ : (structureSheaf B S hS F hF).obj ⟶
      (meromorphicFunctionSheaf B S hS F hF).obj ↦ (φ.app (op Z)).hom z)
    (RingedSite.MultiplicativeSubpresheaf.toLocalizationSheaf_hom
      (regularSectionsSubpresheaf B S hS F hF))

/-- A meromorphic function which multiplies injectively over every chart is locally a unit: let
`x` be a section of `𝒦_F` over an étale scheme chart `U` such that multiplication by the
restriction of `x` is injective on the meromorphic functions over every chart over `U`.  Then the
charts over which `x` restricts to a unit form a covering sieve of `U`. -/
theorem exists_sieve_isUnit_of_injective_mul (U : SmallEtale B S hS F)
    (x : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op U))
    (hinj : ∀ (W : SmallEtale B S hS F) (k : W ⟶ U), Function.Injective
      fun z : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op W) ↦
        z * ((meromorphicFunctionSheaf B S hS F hF).obj.map k.op).hom x) :
    ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS F U ∧
      ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ U), T k →
        IsUnit (((meromorphicFunctionSheaf B S hS F hF).obj.map k.op).hom x) := by
  refine ⟨Presheaf.imageSieve (toSheafify (SmallEtale.topology B S hS F)
      (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf) x,
    imageSieve_toSheafify_localizationPresheaf_mem B S hS F hF U x, ?_⟩
  rintro W k ⟨y, hy⟩
  obtain ⟨b, c, hbc⟩ :=
    IsLocalization.exists_mk'_eq (M := regularSections B S hS F W) y
  have hy' : ((toSheafify (SmallEtale.topology B S hS F)
        (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf).app (op W)).hom y =
      ((meromorphicFunctionSheaf B S hS F hF).obj.map k.op).hom x := hy
  have hkey : ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op W)).hom b =
      ((meromorphicFunctionSheaf B S hS F hF).obj.map k.op).hom x *
        ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op W)).hom
          (c : (structurePresheaf B S hS F).obj (op W)) := by
    rw [toMeromorphicFunctionSheaf_app_apply_eq_toSheafify,
      toMeromorphicFunctionSheaf_app_apply_eq_toSheafify, ← hy', ← hbc]
    have hspec := IsLocalization.mk'_spec
      (ToType ((regularSectionsSubpresheaf B S hS F hF).localizationPresheaf.obj (op W))) b c
    exact (congrArg (fun z ↦ ((toSheafify (SmallEtale.topology B S hS F)
        (regularSectionsSubpresheaf B S hS F hF).localizationPresheaf).app (op W)).hom z)
      hspec.symm).trans (map_mul _ _ _)
  have hcunit : ∀ (Z : SmallEtale B S hS F) (j : Z ⟶ W),
      IsUnit (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
        ((structurePresheaf B S hS F).map j.op
          (c : (structurePresheaf B S hS F).obj (op W)))) := fun Z j ↦
    isUnit_toMeromorphicFunctionSheaf B S hS F hF Z _
      (isRegularSection_map B S hS F j _ c.2)
  have hres : ∀ (Z : SmallEtale B S hS F) (j : Z ⟶ W),
      ((meromorphicFunctionSheaf B S hS F hF).obj.map j.op).hom
          (((meromorphicFunctionSheaf B S hS F hF).obj.map k.op).hom x) =
        ((meromorphicFunctionSheaf B S hS F hF).obj.map (j ≫ k).op).hom x := by
    intro Z j
    rw [op_comp, Functor.map_comp]
    rfl
  have hnat : ∀ (Z : SmallEtale B S hS F) (j : Z ⟶ W)
      (a : (structurePresheaf B S hS F).obj (op W)),
      ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
          ((structurePresheaf B S hS F).map j.op a) =
        ((meromorphicFunctionSheaf B S hS F hF).obj.map j.op).hom
          (((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op W)).hom a) := fun Z j a ↦
    NatTrans.naturality_apply (toMeromorphicFunctionSheaf B S hS F hF).hom j.op a
  have hkeyZ : ∀ (Z : SmallEtale B S hS F) (j : Z ⟶ W),
      ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
          ((structurePresheaf B S hS F).map j.op b) =
        ((meromorphicFunctionSheaf B S hS F hF).obj.map (j ≫ k).op).hom x *
          ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
            ((structurePresheaf B S hS F).map j.op
              (c : (structurePresheaf B S hS F).obj (op W))) := by
    intro Z j
    rw [hnat Z j b, hnat Z j c, hkey, map_mul, hres Z j]
  have hbreg : IsRegularSection B S hS F W b := by
    refine isRegularSection_of_injective_mul_toMeromorphicFunctionSheaf B S hS F hF W b ?_
    intro Z j z z' hzz'
    have e : ∀ w : (meromorphicFunctionSheaf B S hS F hF).obj.obj (op Z),
        w * ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
              ((structurePresheaf B S hS F).map j.op
                (c : (structurePresheaf B S hS F).obj (op W))) *
            ((meromorphicFunctionSheaf B S hS F hF).obj.map (j ≫ k).op).hom x =
          w * ((toMeromorphicFunctionSheaf B S hS F hF).hom.app (op Z)).hom
            ((structurePresheaf B S hS F).map j.op b) := by
      intro w
      rw [hkeyZ Z j, mul_assoc, mul_comm (((meromorphicFunctionSheaf B S hS F hF).obj.map
        (j ≫ k).op).hom x)]
    exact (hcunit Z j).mul_left_injective
      (hinj Z (j ≫ k) ((e z).trans (hzz'.trans (e z').symm)))
  exact isUnit_of_mul_isUnit_left (hkey ▸ isUnit_toMeromorphicFunctionSheaf B S hS F hF W b hbreg)

end AlgebraicGeometry.Space

end
