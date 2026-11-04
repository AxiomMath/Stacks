module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreVanishing
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelSupport
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured

/-!
# The quotient by a nonvanishing section misses the associated points

Let `X` be a scheme, `L` an invertible module on `X` and `σ` a global section of `L`. At a point
near which `σ` does not vanish, the cokernel of multiplication by `σ` on `F ⊗ L^{⊗ n}` has
vanishing stalk. Applied to a coherent triple `T` and a section pair `(σ, σ₀)` of an invertible
triple `L`, this shows that when `σ` does not vanish near the associated points of `T.F`, the
punctured-spectrum member of the cokernel triple of multiplication by `(σ, σ₀)` has support
containing no associated point of `T.F`, and of dimension smaller than that of `Supp T.F`.

## Main results

* `Stacks.Algebraization.notMem_supp_cokernel_tensorModulesMap_id_mulSectionPowScheme`: a point
  near which a global section of `L` does not vanish is not in the support of the cokernel of
  multiplication by that section on `F ⊗ L^{⊗ n}`.
* `Stacks.Algebraization.CoherentTriple.notMem_supp_cokernelTriple_mulSectionTwistZ`: if `σ`
  does not vanish near the associated points of `T.F`, no associated point of `T.F` lies in the
  support of the punctured-spectrum member of the cokernel triple.
* `Stacks.Algebraization.CoherentTriple.dimension_drop_cokernelTriple_mulSectionTwistZ`: under
  the same hypothesis, the support of the punctured-spectrum member of the cokernel triple has
  dimension at most `e` when `Supp T.F` has dimension at most `e + 1`, and is empty when
  `Supp T.F` has dimension `0`.
* `CoherentTriple.eulerCharacteristic_cokernelTriple_mulSectionTwistZ_eq_zero_of_nonvanishing`:
  if the punctured-spectrum member of the cokernel triple vanishes and `σ₀` does not vanish near
  the closed point of the closed fibre, the cokernel triple has Euler characteristic `0`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory IsLocalRing
open Stacks.RelativeVeryAmple
open Stacks.SectionProduct (ofUnitHom)
open Stacks.TensorSectionNonvanishing (mulRight)

universe u

namespace Stacks.Algebraization

/-! The statements below use the monoidal structure `Stacks.Algebraization.strictModulesMonoidal`
on modules, the one in which the twists of a coherent triple are written. -/

attribute [local instance] strictModulesMonoidal

variable {X : Scheme.{u}}

/-! ### The support of the cokernel away from the vanishing of the section -/

/-- Let `L` be an invertible module on `X` and `σ` a global section of `L`. If `σ` does not vanish
on an open neighbourhood `W` of `x`, then `x` is not in the support of the cokernel of
multiplication by `σ` on `F ⊗ L^{⊗ n}`. -/
public theorem notMem_supp_cokernel_tensorModulesMap_id_mulSectionPowScheme (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {N : X.Modules} (n : ℤ)
    (σ : Stacks.Ample.unitModule X ⟶ L)
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (L)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    {W : X.Opens} {x : X} (hx : x ∈ W)
    (hW : ∀ y ∈ W,
      y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L (L.unitHomEquiv σ)) :
    x ∉ SheafOfModules.supp
      (cokernel (tensorModulesMap X (𝟙 F) (mulSectionPowScheme X L σ n))) := by
  have hbij : Function.Bijective (Stacks.ModuleStalk.mapFun
      (mulRight (tensorModules X F (tensorPowScheme X L n)) (ofUnitHom σ)) x) := by
    refine Stacks.SectionProduct.bijective_mapFun_mulRight_of_le_nonvanishingLocus
      (tensorModules X F (tensorPowScheme X L n)) L N ψ (ofUnitHom σ) hx ?_
    intro y hy
    rw [monoidalUnitHomEquiv_ofUnitHom]
    exact hW y hy
  rw [tensorModulesMap_id_eq_whiskerLeft, whiskerLeft_mulSectionPowScheme,
    rightUnitor_inv_comp_whiskerLeft, Category.assoc]
  intro hmem
  exact (AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
      _ x).1 hbij.2
    ((AlgebraicGeometry.Scheme.Modules.supp_cokernel_comp_isIso _ _).subset hmem)

/-! ### Associated points and the support of the cokernel triple -/

/-- If the section `σ` of the invertible triple `L` does not vanish on a neighbourhood of each
associated point of `T.F`, then no associated point of `T.F` lies in the support of the
punctured-spectrum member of the cokernel triple of multiplication by `(σ, σ₀)` on the `m`-th twist
of `T`. -/
public theorem CoherentTriple.notMem_supp_cokernelTriple_mulSectionTwistZ {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (m : ℤ)
    (htf : IsFTorsionFree A f
      (cokernel (T.mulSectionTwistZ L hL σ σ₀ hcompat m).onPunctured))
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints T.F,
      ∃ W : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L.F
          (L.F.unitHomEquiv σ)) :
    ∀ p ∈ Stacks.Divisors.associatedPoints T.F,
      p ∉ SheafOfModules.supp
        (CoherentTriple.cokernelTriple (T.mulSectionTwistZ L hL σ σ₀ hcompat m) htf).F := by
  let := hL.invertible_F
  intro p hp
  obtain ⟨W, hpW, hWloc⟩ := hW p hp
  exact notMem_supp_cokernel_tensorModulesMap_id_mulSectionPowScheme T.F L.F m σ ψ hpW hWloc

/-! ### The dimension drop -/

/-- If the section `σ` of the invertible triple `L` does not vanish on a neighbourhood of each
associated point of `T.F`, then the support of the punctured-spectrum member of the cokernel triple
of multiplication by `(σ, σ₀)` on the `m`-th twist of `T` has dimension at most `e` whenever
`Supp T.F` has dimension at most `e + 1`, and is empty whenever `Supp T.F` has dimension `0`. -/
public theorem CoherentTriple.dimension_drop_cokernelTriple_mulSectionTwistZ {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (m : ℤ)
    (htf : IsFTorsionFree A f
      (cokernel (T.mulSectionTwistZ L hL σ σ₀ hcompat m).onPunctured))
    {N : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules}
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).presheaf,
          (((Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace)).IsSheaf⟩).obj
        (L.F)).obj (N)) ≅
      _root_.SheafOfModules.unit _)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints T.F,
      ∃ W : (Stacks.Divisors.puncturedSpectrum A).toScheme.Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (Stacks.Divisors.puncturedSpectrum A).toScheme.toRingedSpace) L.F
          (L.F.unitHomEquiv σ)) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim ↥(SheafOfModules.supp
          (CoherentTriple.cokernelTriple (T.mulSectionTwistZ L hL σ σ₀ hcompat m) htf).F) ≤
            ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp
          (CoherentTriple.cokernelTriple (T.mulSectionTwistZ L hL σ σ₀ hcompat m) htf).F = ∅) :=
  T.dimension_drop_cokernelTriple_twistZ_of_notMem_associatedPoints L hL _ htf
    (T.notMem_supp_cokernelTriple_mulSectionTwistZ L hL σ σ₀ hcompat m htf ψ hW)

/-! ### The Euler characteristic when the section does not vanish at the closed point -/

/-- For a Noetherian local ring `A` and a regular `f` in the maximal ideal, if the
punctured-spectrum member of the cokernel triple of multiplication by `(σ, σ₀)` on the `m`-th twist
of `T` vanishes and `σ₀` does not vanish on a neighbourhood of the closed point of the closed
fibre, then that cokernel triple has Euler characteristic `0`. -/
public theorem
    CoherentTriple.eulerCharacteristic_cokernelTriple_mulSectionTwistZ_eq_zero_of_nonvanishing
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀)
    (hcompat :
      ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀)
    (m : ℤ)
    (htf : IsFTorsionFree A f
      (cokernel (T.mulSectionTwistZ L hL σ σ₀ hcompat m).onPunctured))
    (hzero : IsZero
      (CoherentTriple.cokernelTriple (T.mulSectionTwistZ L hL σ σ₀ hcompat m) htf).F)
    {N₀ : (closedFibre A f).Modules}
    (ψ₀ : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((closedFibre A f).toRingedSpace)).presheaf,
          (((closedFibre A f).toRingedSpace)).IsSheaf⟩).obj (L.F₀)).obj (N₀)) ≅
      _root_.SheafOfModules.unit _)
    {W₀ : (closedFibre A f).Opens}
    (hx : (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) : closedFibre A f) ∈ W₀)
    (hW₀ : ∀ y ∈ W₀, y ∈ Stacks.SheafOfModules.nonvanishingLocus
      (X := (closedFibre A f).toRingedSpace) L.F₀ (L.F₀.unitHomEquiv σ₀)) :
    (CoherentTriple.cokernelTriple (T.mulSectionTwistZ L hL σ σ₀ hcompat m)
      htf).eulerCharacteristic hf hreg = 0 :=
  let := hL.invertible_F₀
  CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F hf hreg _ hzero fun hass =>
    notMem_supp_cokernel_tensorModulesMap_id_mulSectionPowScheme T.F₀ L.F₀ m σ₀ ψ₀ hx hW₀
      (AlgebraicGeometry.associatedPoints_subset_support _ hass)

end Stacks.Algebraization

end
