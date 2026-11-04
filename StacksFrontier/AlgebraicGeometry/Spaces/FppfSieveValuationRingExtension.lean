module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedSeparatedValuative
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# Covering sieves over the spectrum of a valuation ring

Let `R` be a valuation ring whose spectrum belongs to the big fppf site of `S`. A covering sieve
of `Spec R` for the fppf topology contains, after an extension of valuation rings `R ⟶ R'`, the
morphism `Spec R' ⟶ Spec R` itself. This is the form in which an fppf-local statement over the
spectrum of a valuation ring becomes a statement over an extension of it, as in the proof of
Stacks 0DNJ: a point of the relative Picard functor over `Spec R` is only fppf locally the class
of an invertible module, and so is the class of an invertible module after an extension of `R`.

## Main results

* `AlgebraicGeometry.Space.exists_valuationRing_extension_mem_of_mem_topology`: a covering sieve
  of the fppf topology on `Spec R` contains `Spec R' ⟶ Spec R` for some extension of valuation
  rings `R ⟶ R'` whose spectrum belongs to the site.

## Implementation notes

The covering sieve contains a flat, locally finitely presented and jointly surjective family
(`AlgebraicGeometry.exists_family_of_mem_topology`); a member `W ⟶ Spec R` of it has a point
over the closed point of `Spec R`, and Stacks 089F,
`AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat`, applied to the flat
morphism of represented algebraic spaces it defines, lifts `Spec R` to `W` after an extension of
valuation rings. The sieve, being closed under precomposition, then contains the composite
`Spec R' ⟶ W ⟶ Spec R`.

## References

* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A covering sieve over the spectrum of a valuation ring contains the spectrum of an
extension.** Let `R` be a valuation ring whose spectrum belongs to the big fppf site, over `S`
through `base`. Every covering sieve of `Spec R` for the fppf topology contains the morphism
`Spec R' ⟶ Spec R` of some extension of valuation rings `R ⟶ R'` whose spectrum belongs to the
site. -/
theorem exists_valuationRing_extension_mem_of_mem_topology
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (ring_mem : B.Contains (Spec (.of R))) (base : Spec (.of R) ⟶ S)
    {Sv : Sieve (siteObject B S hS ring_mem base)}
    (hSv : Sv ∈ BigFppfOver.topology B S hS (siteObject B S hS ring_mem base)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (φ : R →+* R'), ValuationRing.IsExtension φ ∧
      ∃ ring_mem' : B.Contains (Spec (.of R')),
        Sv.arrows (specSiteObjectMap φ ring_mem ring_mem' base) := by
  obtain ⟨I, W, m, hmem, hflat, _, hsurj⟩ := exists_family_of_mem_topology B S hS hSv
  obtain ⟨i, w, hw⟩ := hsurj (IsLocalRing.closedPoint R)
  set Wi : BigFppfOver B S hS := Over.mk (m i ≫ (siteObject B S hS ring_mem base).hom) with hWi
  set h : Wi ⟶ siteObject B S hS ring_mem base := Over.homMk (m i) with hh
  have hhflat : IsFlat B S hS (yoneda.map h) := isFlat_yoneda_map B S hS h (hflat i)
  set p := FieldValuedPoint.map B S hS (yoneda.obj Wi) (yoneda.map h)
    (schemePointRepresentative B S hS Wi w) with hp
  have hpt :
      schemePoint B S hS (siteObject B S hS ring_mem base) p = IsLocalRing.closedPoint R := by
    rw [hp, schemePoint_map_yoneda, schemePointRepresentative_point]
    exact hw
  obtain ⟨R', _, _, _, φ, hext, V', e', j, lift, hj, hlift⟩ :=
    exists_valuationRing_extension_lift_of_isFlat R (isAlgebraicSpace_yoneda B S hS Wi)
      (isAlgebraicSpace_yoneda B S hS (siteObject B S hS ring_mem base)) (yoneda.map h) hhflat
      (siteObject B S hS ring_mem base) (Iso.refl _) (𝟙 _) p hpt
      ⟨(schemePointRepresentative B S hS Wi w).class B S hS (yoneda.obj Wi), by
        rw [pointsMap_class, pointsMap_class, FieldValuedPoint.map_id]⟩
  have ring_mem' : B.Contains (Spec (.of R')) :=
    Scheme.size_lt_of_mono_quasiCompact e'.inv V'.left.property
  refine ⟨R', inferInstance, inferInstance, inferInstance, φ, hext, ring_mem', ?_⟩
  have hj' : (BigFppfOver.toScheme B S hS).map j = e'.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    simpa using hj
  have hV'hom : B.inclusion.map V'.hom = (BigFppfOver.toScheme B S hS).map j ≫ base := by
    rw [← Over.w j]
    rfl
  set k : siteObject B S hS ring_mem' (Spec.map (CommRingCat.ofHom φ) ≫ base) ⟶ V' :=
    Over.homMk (B.inclusion.preimage (X := B.obj ring_mem') (Y := V'.left) e'.inv) (by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, hV'hom, hj', Category.assoc,
        Iso.inv_hom_id_assoc]
      rfl) with hk
  have hjfac : j = yoneda.preimage lift ≫ h := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, hlift, Category.comp_id]
  have heq : specSiteObjectMap φ ring_mem ring_mem' base =
      k ≫ j := by
    apply siteObject_hom_ext
    change Spec.map (CommRingCat.ofHom φ) =
      B.inclusion.map (B.inclusion.preimage (X := B.obj ring_mem') (Y := V'.left) e'.inv) ≫
        (BigFppfOver.toScheme B S hS).map j
    rw [Functor.map_preimage, hj', Iso.inv_hom_id_assoc]
  rw [heq, hjfac, ← Category.assoc]
  exact Sv.downward_closed (hmem i) _

end AlgebraicGeometry.Space

end
