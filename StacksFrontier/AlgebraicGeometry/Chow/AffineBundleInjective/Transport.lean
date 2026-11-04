module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.FibreStatements

/-!
# The fibrewise properties are local on the target

Let `(S, δ)` be the base situation of chapter 42. The two fibrewise properties
`Stacks.Chow.FibreBoundaryLift` and `Stacks.Chow.FibreUnitDescent` of a morphism `f : X ⟶ Y` at a
point `y` only see the fibre over `y` and the local rings of the closures of its points. This file
proves that they pass along a square

```
X' --jX--> X
|f'        |f
Y' --jY--> Y
```

of open immersions in which `X'` contains the whole inverse image of the image of `Y'`: from
`f'` at `y'` to `f` at `jY y'`. Chains on `X` supported over `jY y'` are restricted to `X'` and,
conversely, chains on `X'` are extended by zero, and both operations commute with the two
differentials of Stacks 0GU9 (Stacks 0GUA, `Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary`
and `Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential`). An isomorphism of arrows is the
special case of a square of isomorphisms.

## Main results

* `Stacks.Chow.fibreBoundaryLift_of_openSquare`
* `Stacks.Chow.fibreUnitDescent_of_openSquare`

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

section Comap

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (jX : X' ⟶ X) [IsOpenImmersion jX]

/-- Restriction of chains to an open subscheme along an open immersion. -/
abbrev openComap (m : ℤ) (n : ℕ) : MilnorChainGroup C sX m n →+ MilnorChainGroup C (jX ≫ sX) m n :=
  milnorChainComap C sX jX (injective_base_of_isOpenImmersion jX)
    (bijective_residueFieldMap_openImmersion jX) m n

/-- Extension of chains by zero along an open immersion. -/
abbrev openExtend (m : ℤ) (n : ℕ) : MilnorChainGroup C (jX ≫ sX) m n →+ MilnorChainGroup C sX m n :=
  milnorChainExtend C sX jX (injective_base_of_isOpenImmersion jX)
    (bijective_residueFieldMap_openImmersion jX)
    (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType sX jX) m n

omit [LocallyOfFiniteType sX] in
/-- Restriction to an open subscheme commutes with restriction to a set of points. -/
theorem openComap_milnorChainRestrict (T : Set X) (m : ℤ) (n : ℕ) (a : MilnorChainGroup C sX m n) :
    openComap C sX jX m n (milnorChainRestrict C sX T m n a) =
      milnorChainRestrict C (jX ≫ sX) (jX.base ⁻¹' T) m n (openComap C sX jX m n a) := by
  refine Subtype.ext (funext fun z ↦ ?_)
  by_cases hz : jX.base z.1 ∈ T
  · rw [milnorChainRestrict_apply_of_mem _ (show z.1 ∈ jX.base ⁻¹' T from hz),
      milnorChainComap_apply, milnorChainComap_apply,
      milnorChainRestrict_apply_of_mem (x := immersionPoint C sX jX
        (bijective_residueFieldMap_openImmersion jX) m z) _ hz]
  · rw [milnorChainRestrict_apply_of_notMem _ (show z.1 ∉ jX.base ⁻¹' T from hz),
      milnorChainComap_apply,
      milnorChainRestrict_apply_of_notMem (x := immersionPoint C sX jX
        (bijective_residueFieldMap_openImmersion jX) m z) _ hz, map_zero]

/-- An extension by zero is supported in the image. -/
theorem mem_range_of_openExtend_apply_ne_zero {m : ℤ} {n : ℕ}
    (b : MilnorChainGroup C (jX ≫ sX) m n) {x : pointsOfDimension C sX m}
    (h : (openExtend C sX jX m n b).1 x ≠ 0) : (x : X) ∈ Set.range jX.base := by
  by_contra hx
  exact h (by rw [milnorChainExtend_apply, milnorChainExtendAtHom_of_notMem_range C sX jX _ x hx,
    AddMonoidHom.zero_apply])

/-- Restricting an extension by zero returns the chain. -/
theorem openComap_openExtend {m : ℤ} {n : ℕ} (b : MilnorChainGroup C (jX ≫ sX) m n) :
    openComap C sX jX m n (openExtend C sX jX m n b) = b :=
  DFunLike.congr_fun (milnorChainComap_milnorChainExtend C sX jX
    (injective_base_of_isOpenImmersion jX) (bijective_residueFieldMap_openImmersion jX)
    (quasiCompact_of_isOpenImmersion_of_locallyOfFiniteType sX jX) m n) b

omit [LocallyOfFiniteType sX] in
/-- **Two chains supported in the image of an open immersion are determined by their
restrictions.** -/
theorem eq_of_openComap_eq {m : ℤ} {n : ℕ} {a b : MilnorChainGroup C sX m n}
    (ha : ∀ x : pointsOfDimension C sX m, a.1 x ≠ 0 → (x : X) ∈ Set.range jX.base)
    (hb : ∀ x : pointsOfDimension C sX m, b.1 x ≠ 0 → (x : X) ∈ Set.range jX.base)
    (h : openComap C sX jX m n a = openComap C sX jX m n b) : a = b := by
  refine Subtype.ext (funext fun x ↦ ?_)
  by_cases hx : (x : X) ∈ Set.range jX.base
  · obtain ⟨z, rfl⟩ := exists_immersionPoint_eq C sX jX
      (bijective_residueFieldMap_openImmersion jX) x hx
    have := congrArg (fun c : MilnorChainGroup C (jX ≫ sX) m n ↦ c.1 z) h
    simp only [milnorChainComap_apply] at this
    exact (milnorKTransport_bijective _ n).1 this
  · rw [not_imp_comm.1 (ha x) hx, not_imp_comm.1 (hb x) hx]

end Comap

section Square

variable (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (f' : X' ⟶ Y')
  (jX : X' ⟶ X) [IsOpenImmersion jX] (jY : Y' ⟶ Y) [IsOpenImmersion jY]
  (hsq : jX ≫ f = f' ≫ jY) (hpre : f.base ⁻¹' Set.range jY.base ⊆ Set.range jX.base)

include hsq in
omit [IsOpenImmersion jX] in
/-- The fibre of `f'` over `y'` is the preimage of the fibre of `f` over `jY y'`. -/
theorem preimage_fibre_of_openSquare (y' : Y') :
    jX.base ⁻¹' (f.base ⁻¹' {jY.base y'}) = f'.base ⁻¹' {y'} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
  exact (injective_base_of_isOpenImmersion jY).eq_iff

include hpre in
omit [LocallyOfFiniteType sX] [IsOpenImmersion jX] [IsOpenImmersion jY] in
/-- A point where a chain restricted to the fibre over `jY y'` is nonzero lies in the image of
`jX`. -/
theorem mem_range_of_fibreRestrict_apply_ne_zero {m : ℤ} {n : ℕ} {y' : Y'}
    {a : MilnorChainGroup C sX m n} {x : pointsOfDimension C sX m}
    (hx : (fibreRestrict C sX f (jY.base y') m n a).1 x ≠ 0) : (x : X) ∈ Set.range jX.base := by
  have hfx : f.base x.1 = jY.base y' := by
    by_contra hne
    exact hx (milnorChainRestrict_apply_of_notMem _ hne)
  exact hpre ⟨y', hfx.symm⟩

include hsq hpre in
omit [LocallyOfFiniteType sX] [IsOpenImmersion jX] [IsOpenImmersion jY] in
/-- A chain on `X` supported over `jY y'` lives in the image of `jX`. -/
theorem mem_range_of_fibreRestrict_eq_self {m : ℤ} {n : ℕ} {y' : Y'}
    {a : MilnorChainGroup C sX m n} (ha : fibreRestrict C sX f (jY.base y') m n a = a)
    {x : pointsOfDimension C sX m} (hx : a.1 x ≠ 0) : (x : X) ∈ Set.range jX.base := by
  rw [← ha] at hx
  exact mem_range_of_fibreRestrict_apply_ne_zero C sX f jX jY hpre hx

variable {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {sY' : Y' ⟶ C.S} [LocallyOfFiniteType sY']

include hsq hpre in
omit [LocallyOfFiniteType sY] in
/-- **The boundary-lifting property passes along a square of open immersions.** -/
theorem fibreBoundaryLift_of_openSquare (hX : jX ≫ sX = sX') (hY : jY ≫ sY = sY') (r : ℕ)
    (k : ℤ) (y' : Y') (h : FibreBoundaryLift C sX' sY' f' r k y') :
    FibreBoundaryLift C sX sY f r k (jY.base y') := by
  subst hX hY
  intro hdim a ha hdiv
  have hdim' : relativeDimension C.dimensionFunction (jY ≫ sY) y' ≠ k + 1 - r := by
    rwa [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction jY sY y'
      (bijective_residueFieldMap_openImmersion jY y')]
  have hpref := preimage_fibre_of_openSquare f f' jX jY hsq y'
  obtain ⟨η', hη'sup, hη'⟩ := h hdim' (openComap C sX jX (k + 1) 1 a) (by
      rw [fibreRestrict, ← hpref, ← openComap_milnorChainRestrict, ← fibreRestrict, ha]) (by
      have := DFunLike.congr_fun (milnorChainComap_pointwiseDivisorDifferential C sX jX k) a
      simp only [AddMonoidHom.comp_apply] at this
      rw [fibreRestrict, ← hpref, this, ← openComap_milnorChainRestrict, ← fibreRestrict, hdiv,
        map_zero])
  refine ⟨openExtend C sX jX (k + 2) 2 η', ?_, ?_⟩
  · refine eq_of_openComap_eq C sX jX
      (fun _ hx ↦ mem_range_of_fibreRestrict_apply_ne_zero C sX f jX jY hpre hx)
      (fun _ hx ↦ mem_range_of_openExtend_apply_ne_zero C sX jX _ hx) ?_
    rwa [fibreRestrict, openComap_milnorChainRestrict, hpref, openComap_openExtend]
  · refine eq_of_openComap_eq C sX jX
      (fun _ hx ↦ mem_range_of_fibreRestrict_apply_ne_zero C sX f jX jY hpre hx)
      (fun _ hx ↦ mem_range_of_fibreRestrict_eq_self C sX f f' jX jY hsq hpre ha hx) ?_
    rw [fibreRestrict, openComap_milnorChainRestrict, hpref]
    have := DFunLike.congr_fun (milnorChainComap_pointwiseMilnorBoundary C sX jX k)
      (openExtend C sX jX (k + 2) 2 η')
    simp only [AddMonoidHom.comp_apply] at this
    rwa [← this, openComap_openExtend]

/-- Two residue field identifications along equalities of points, there and back, cancel. -/
theorem residueFieldCongr_hom_comp_hom_comp {Y : Scheme.{u}} {a b : Y} (p : a = b) (q : b = a)
    {R : CommRingCat.{u}} (g : Y.residueField a ⟶ R) :
    (Y.residueFieldCongr p).hom ≫ (Y.residueFieldCongr q).hom ≫ g = g := by
  subst p
  rw [Scheme.residueFieldCongr_refl]
  simp

include hsq in
omit [IsOpenImmersion jX] [IsOpenImmersion jY] in
/-- The two ways around a commutative square agree on points. -/
theorem openSquare_base_apply (ξ' : X') : jY.base (f'.base ξ') = f.base (jX.base ξ') :=
  (congrArg (fun g : X' ⟶ Y ↦ g.base ξ') hsq).symm

include hsq in
omit [IsOpenImmersion jX] in
/-- The residue field maps of the two vertical arrows of a commutative square of open immersions
are identified by the residue field isomorphisms of the horizontal arrows. -/
theorem residueFieldMap_openSquare_apply (ξ' : X') (c : Y'.residueField (f'.base ξ')) :
    (jX.residueFieldMap ξ').hom ((f.residueFieldMap (jX.base ξ')).hom
        ((Y.residueFieldCongr (openSquare_base_apply f f' jX jY hsq ξ')).hom.hom
          ((immersionResidueFieldEquiv jY (bijective_residueFieldMap_openImmersion jY)
            (f'.base ξ')).symm c))) =
      (f'.residueFieldMap ξ').hom c := by
  set c₀ := (immersionResidueFieldEquiv jY (bijective_residueFieldMap_openImmersion jY)
    (f'.base ξ')).symm c
  have hc : (jY.residueFieldMap (f'.base ξ')).hom c₀ = c :=
    (immersionResidueFieldEquiv jY (bijective_residueFieldMap_openImmersion jY)
      (f'.base ξ')).apply_symm_apply c
  rw [← hc]
  have hcomp := Scheme.Hom.residueFieldMap_congr hsq ξ'
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hcomp
  have hhom : (Y.residueFieldCongr (openSquare_base_apply f f' jX jY hsq ξ')).hom ≫
      f.residueFieldMap (jX.base ξ') ≫ jX.residueFieldMap ξ' =
      jY.residueFieldMap (f'.base ξ') ≫ f'.residueFieldMap ξ' := by
    rw [hcomp]
    exact residueFieldCongr_hom_comp_hom_comp _ _ _
  exact congrArg (fun φ ↦ φ.hom c₀) hhom

include hsq hpre in
omit [LocallyOfFiniteType sY] in
/-- **The unit-descent property passes along a square of open immersions.** -/
theorem fibreUnitDescent_of_openSquare (hX : jX ≫ sX = sX') (hY : jY ≫ sY = sY') (r : ℕ)
    (k : ℤ) (y' : Y') (h : FibreUnitDescent C sX' sY' f' r k y') :
    FibreUnitDescent C sX sY f r k (jY.base y') := by
  subst hX hY
  intro hdim a ha hdiv ξ hξ
  have hdim' : relativeDimension C.dimensionFunction (jY ≫ sY) y' = k + 1 - r := by
    rwa [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction jY sY y'
      (bijective_residueFieldMap_openImmersion jY y')]
  have hpref := preimage_fibre_of_openSquare f f' jX jY hsq y'
  obtain ⟨z, hz⟩ := exists_immersionPoint_eq C sX jX
    (bijective_residueFieldMap_openImmersion jX) ξ (hpre ⟨y', hξ.symm⟩)
  have hfz : f'.base z.1 = y' := injective_base_of_isOpenImmersion jY (by
    rw [openSquare_base_apply f f' jX jY hsq, show jX.base z.1 = ξ.1 from congrArg Subtype.val hz,
      hξ])
  obtain ⟨c', hc'⟩ := h hdim' (openComap C sX jX (k + 1) 1 a) (by
      rw [fibreRestrict, ← hpref, ← openComap_milnorChainRestrict, ← fibreRestrict, ha]) (by
      have := DFunLike.congr_fun (milnorChainComap_pointwiseDivisorDifferential C sX jX k) a
      simp only [AddMonoidHom.comp_apply] at this
      rw [fibreRestrict, ← hpref, this, ← openComap_milnorChainRestrict, ← fibreRestrict, hdiv,
        map_zero]) z hfz
  subst hz
  rw [milnorChainComap_apply] at hc'
  set ψ : Y'.residueField (f'.base z.1) →+* Y.residueField (f.base (jX.base z.1)) :=
    ((Y.residueFieldCongr (openSquare_base_apply f f' jX jY hsq z.1)).hom.hom).comp
      ((immersionResidueFieldEquiv jY (bijective_residueFieldMap_openImmersion jY)
        (f'.base z.1)).symm : _ →+* _)
  refine ⟨milnorKTransport ψ 1 c', ?_⟩
  apply (milnorKTransport_bijective
    (immersionResidueFieldEquiv jX (bijective_residueFieldMap_openImmersion jX) z.1) 1).1
  rw [hc', milnorKTransport_comp_apply, milnorKTransport_comp_apply]
  exact congrArg (fun φ ↦ milnorKTransport φ 1 c')
    (RingHom.ext fun c ↦ (residueFieldMap_openSquare_apply f f' jX jY hsq z.1 c).symm)

end Square

end Stacks.Chow

end
