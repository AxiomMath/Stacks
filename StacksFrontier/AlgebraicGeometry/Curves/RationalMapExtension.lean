module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticClosure
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.Extension
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Rational maps from normal curves to proper varieties

Let `k` be a field, let `X` be a normal curve over `k` and let `Y` be a proper variety over `k`.
Every rational map `X ⇢ Y` over `k` is the rational map of a unique morphism `X ⟶ Y` over `k`.
Both halves come from the one-dimensionality of `X`: a point of `X` other than the generic point
is closed, so the local ring there is a discrete valuation ring and a morphism defined on a dense
open extends across it; and a dense open of a reduced scheme is scheme-theoretically dense, so
two morphisms agreeing on one are equal.

## Main results

* `AlgebraicGeometry.toRationalMap_bijective`: passing from a morphism over `k` to its rational
  map is a bijection onto the rational maps over `k`.

## Implementation notes

Varieties and their maps live over `Spec k`, so a morphism is a morphism of the over category
`CategoryTheory.Over (Spec k)` while a rational map is one of Mathlib's
`AlgebraicGeometry.Scheme.RationalMap`s cut down by `AlgebraicGeometry.Scheme.RationalMap.IsOver`.
The equality of sets asserted by the source is therefore stated as bijectivity of the canonical
map from the morphisms to the subtype of rational maps over the base.

## References

* [Stacks Project, Tag 0BXZ](https://stacks.math.columbia.edu/tag/0BXZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The underlying scheme of a proper variety is separated. -/
private theorem isSeparated_left_of_isProperVariety (k : Type u) [Field k]
    (Y : Over (Spec (.of k))) [IsProperVariety k Y.hom] : Y.left.IsSeparated := by
  have : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  constructor
  rw [← terminal.comp_from Y.hom]
  infer_instance

/-- Morphisms over the base from a normal curve to a proper variety agreeing as rational maps
are equal. -/
private theorem toRationalMap_injective
    (k : Type u) [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsNormal X.left] [IsProperVariety k Y.hom] :
    Function.Injective
      (fun f : X ⟶ Y ↦
        (⟨f.left.toRationalMap, inferInstance⟩ :
          {g : Scheme.RationalMap X.left Y.left // g.IsOver (Spec (.of k))})) := by
  intro f g hfg
  let pf : X.left.PartialMap Y.left := f.left.toPartialMap
  let pg : X.left.PartialMap Y.left := g.left.toPartialMap
  obtain ⟨U, hU, hUl, hUr, hEq⟩ :=
    Scheme.PartialMap.toRationalMap_eq_iff.mp (congrArg Subtype.val hfg :
      pf.toRationalMap = pg.toRationalMap)
  change X.left.homOfLE hUl ≫ pf.hom = X.left.homOfLE hUr ≫ pg.hom at hEq
  have key (h : X.left ⟶ Y.left) (hU : U ≤ h.toPartialMap.domain) :
      U.ι ≫ h = X.left.homOfLE hU ≫ h.toPartialMap.hom := by
    simp [Scheme.Hom.toPartialMap, Scheme.topIso_hom, ← Scheme.homOfLE_ι X.left hU]
  have hfgU : U.ι ≫ f.left = U.ι ≫ g.left :=
    (key f.left hUl).trans (hEq.trans (key g.left hUr).symm)
  exact eq_of_isSchemeTheoreticallyDense f g U (((dense_open_tfae U).out 1 3).mp hU) hfgU

/-- A rational map over the base from a normal curve to a proper variety is defined
everywhere. -/
private theorem Scheme.RationalMap.domain_eq_top_of_isCurve
    (k : Type u) [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsNormal X.left] [IsProperVariety k Y.hom]
    (r : Scheme.RationalMap X.left Y.left) [r.IsOver (Spec (.of k))] :
    r.domain = ⊤ := by
  have := isSeparated_left_of_isProperVariety k Y
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := IsNoetherian.mk
  let p : X.left.PartialMap Y.left := r.toPartialMap
  have hpOver : p.IsOver (Spec (.of k)) := inferInstance
  have hpDense : Dense (p.domain : Set X.left) := p.dense_domain
  obtain ⟨x₀, hx₀⟩ := hpDense.nonempty
  have hgeneric : genericPoint X.left ∈ p.domain :=
    (genericPoint_spec X.left).mem_open_set_iff p.domain.2 |>.mpr
      ⟨x₀, Set.mem_univ _, hx₀⟩
  refine top_unique fun x _ ↦ ?_
  by_contra hnot
  have hxne : x ≠ genericPoint X.left := by
    rintro rfl
    exact hnot hgeneric
  have hxclosed : IsClosed ({x} : Set X.left) :=
    Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
      X.left (IsCurve.topologicalKrullDim_eq_one (k := k) (f := X.hom)) hxne
  have : IsIntegrallyClosed (X.left.presheaf.stalk x) := IsNormal.stalk_normal x
  have : IsDiscreteValuationRing (X.left.presheaf.stalk x) :=
    ((isDiscreteValuationRing_stalk_tfae_of_isCurve k X.hom hxclosed).out 2 3).mp
      (IsNormalRing.of_isIntegrallyClosed _)
  obtain ⟨U', hUU', hxU', f', hfBase, hfRestr⟩ :=
    exists_open_extension_of_valuationRing_stalk
      X.hom Y.hom x p.domain p.hom
      (Scheme.PartialMap.isOver_iff.mp hpOver)
      (by simp [hpDense.closure_eq])
      (Or.inr inferInstance)
  let p' : X.left.PartialMap Y.left := ⟨U', hpDense.mono hUU', f'⟩
  have hp'Eq : p'.toRationalMap = p.toRationalMap := by
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨p.domain, hpDense, hUU', le_rfl, ?_⟩
    change X.left.homOfLE hUU' ≫ f' = X.left.homOfLE le_rfl ≫ p.hom
    simp [hfRestr]
  have hmem : x ∈ (p'.toRationalMap).domain :=
    Scheme.RationalMap.mem_domain.mpr ⟨p', hxU', rfl⟩
  rw [hp'Eq.trans (Scheme.RationalMap.toRationalMap_toPartialMap r)] at hmem
  exact hnot hmem

/-- Every rational map over the base from a normal curve to a proper variety is the rational
map of a morphism over the base. -/
private theorem toRationalMap_surjective
    (k : Type u) [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsNormal X.left] [IsProperVariety k Y.hom] :
    Function.Surjective
      (fun f : X ⟶ Y ↦
        (⟨f.left.toRationalMap, inferInstance⟩ :
          {g : Scheme.RationalMap X.left Y.left // g.IsOver (Spec (.of k))})) := by
  rintro ⟨r, hr⟩
  have := isSeparated_left_of_isProperVariety k Y
  let p : X.left.PartialMap Y.left := r.toPartialMap
  have hdomain : p.domain = ⊤ := Scheme.RationalMap.domain_eq_top_of_isCurve k X Y r
  have hpOver : p.IsOver (Spec (.of k)) := inferInstance
  let e : p.domain.toScheme ≅ X.left := X.left.isoOfEq hdomain ≪≫ Scheme.topIso X.left
  let gleft : X.left ⟶ Y.left := e.inv ≫ p.hom
  have heInvι : e.inv ≫ p.domain.ι = 𝟙 X.left := by
    calc
      e.inv ≫ p.domain.ι = X.left.topIso.inv ≫
          ((X.left.isoOfEq hdomain).inv ≫ p.domain.ι) := by simp [e]
      _ = X.left.topIso.inv ≫ (⊤ : X.left.Opens).ι := by
        rw [Scheme.isoOfEq_inv_ι]
      _ = 𝟙 X.left := by simp
  have hpBase : p.hom ≫ Y.hom = p.domain.ι ≫ X.hom := Scheme.PartialMap.isOver_iff.mp hpOver
  have hgleftOver : gleft ≫ Y.hom = X.hom := by
    change e.inv ≫ (p.hom ≫ Y.hom) = X.hom
    rw [hpBase, ← Category.assoc, heInvι]
    simp
  have hpartial : p = gleft.toPartialMap := by
    refine Scheme.PartialMap.ext p gleft.toPartialMap hdomain ?_
    change p.hom = e.hom ≫ e.inv ≫ p.hom
    simp only [Iso.hom_inv_id_assoc]
  exact ⟨Over.homMk gleft hgleftOver,
    Subtype.ext <| (congrArg Scheme.PartialMap.toRationalMap hpartial).symm.trans
      (Scheme.RationalMap.toRationalMap_toPartialMap r)⟩

/-- **Stacks Project, Tag 0BXZ.** Morphisms from a normal curve to a proper variety are in
canonical bijection with the rational maps over the base field. -/
@[stacks 0BXZ, ega "II 7.4.9"]
theorem toRationalMap_bijective
    (k : Type u) [Field k] (X Y : Over (Spec (.of k)))
    [IsCurve k X.hom] [IsNormal X.left] [IsProperVariety k Y.hom] :
    Function.Bijective
      (fun f : X ⟶ Y ↦
        (⟨f.left.toRationalMap, inferInstance⟩ :
          {g : Scheme.RationalMap X.left Y.left // g.IsOver (Spec (.of k))})) :=
  ⟨toRationalMap_injective k X Y, toRationalMap_surjective k X Y⟩

end AlgebraicGeometry

end
