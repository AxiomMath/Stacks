module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorCupVanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.AxiomsBasic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Coproduct
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.SmoothDivisor

/-!
# Axiom (A4) for Hodge cohomology, on `H^*_{Hodge}(X/k)`

Let `X` and `Y` be smooth projective over a field `k` and `i : Y ⟶ X` the inclusion of an
effective Cartier divisor `D`. This file assembles, on the graded algebra
`H^*_{Hodge}(X/k) = ⨁_n ⨁_{p+q=n} H^q(X, Ω^p_{X/k})`, the vanishing
`Stacks.HodgeWeil.hodgeComponentCup_eq_zero_of_logPoles` of the cup products of pure bidegree: if
`c ∈ H^1(X, Ω^1_{X/k})` dies in `H^1(X, Ω^1_{X/k}(log D))` and `i^* a = 0`, then `a ∪ c = 0`.
The de Rham complex of log poles is defined for `D ⊆ X` because `X` and `D ≅ Y` are smooth over
`k` (Tag 0FMY), and the pullback along `i` vanishes on a class exactly when the pullback along the
inclusion of `D` does, `i` being that inclusion composed with an isomorphism.

## Main results

* `Stacks.HodgeWeil.hasLogPolesDeRhamComplex_of_divisor`: the log poles condition.
* `Stacks.HodgeWeil.hodgePullback_subschemeι_eq_zero`: vanishing of the pullback along `D`.
* `Stacks.HodgeWeil.mul_hodgeClass_eq_zero_of_pull_eq_zero`: **`a ∪ c = 0` in
  `H^*_{Hodge}(X/k)`** for `i^* a = 0`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FMY](https://stacks.math.columbia.edu/tag/0FMY)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyMap)
open AlgebraicGeometry.SheafOfModules (baseRingedSpace hodgeCohomologyComponent
  toHodgeComponentBase)

universe u

namespace Stacks.HodgeWeil

variable {k : Type u} [Field k] {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- The divisor inclusion and `Y` have the same structure map to `Spec k`, up to `e`. -/
private theorem iso_hom_comp_subschemeι_comp_hom (i : Y ⟶ X)
    (D : ((toScheme k).obj X).IdealSheafData)
    (e : (toScheme k).obj Y ≅ D.subscheme) (he : e.hom ≫ D.subschemeι = (toScheme k).map i) :
    e.hom ≫ D.subschemeι ≫ X.obj.hom = Y.obj.hom ≫ 𝟙 _ := by
  rw [← Category.assoc, he, Category.comp_id]
  exact Over.w i.hom

/-- **The de Rham complex of log poles is defined for a smooth divisor of a smooth scheme**
(Tag 0FMY): `X ⟶ Spec k` is smooth and the divisor `D ≅ Y` is smooth over `k`. -/
theorem hasLogPolesDeRhamComplex_of_divisor (i : Y ⟶ X)
    (D : ((toScheme k).obj X).IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (e : (toScheme k).obj Y ≅ D.subscheme) (he : e.hom ≫ D.subschemeι = (toScheme k).map i) :
    X.obj.hom.HasLogPolesDeRhamComplex D := by
  have : Smooth X.obj.hom := X.property.1
  have : Smooth (D.subschemeι ≫ X.obj.hom) := by
    have h : D.subschemeι ≫ X.obj.hom = e.inv ≫ Y.obj.hom := by
      rw [← cancel_epi e.hom, Iso.hom_inv_id_assoc,
        iso_hom_comp_subschemeι_comp_hom i D e he, Category.comp_id]
    rw [h]
    have : Smooth Y.obj.hom := Y.property.1
    infer_instance
  have h := Scheme.Hom.hasLogPolesDeRhamComplex_of_smooth X.obj.hom (𝟙 _) D hD
  rwa [Category.comp_id] at h


/-- **The pullback along `i` kills a Hodge class exactly when the pullback along the inclusion
of the divisor does**; here the direction used: if `i^* x = 0` then `x` restricts to zero on
`D`, since `i` is the inclusion of `D` composed with the isomorphism `e`. -/
theorem hodgePullback_subschemeι_eq_zero (i : Y ⟶ X)
    (D : ((toScheme k).obj X).IdealSheafData)
    (e : (toScheme k).obj Y ≅ D.subscheme) (he : e.hom ≫ D.subschemeι = (toScheme k).map i)
    (p : ℕ) (q : ℤ) (x : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras X.obj.hom) p q)
    (hx : hodgePullback i.hom.left Y.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w i) p q x = 0) :
    hodgePullback D.subschemeι (D.subschemeι ≫ X.obj.hom) X.obj.hom (𝟙 _)
      (subschemeι_square X.obj.hom D) p q x = 0 := by
  have we := iso_hom_comp_subschemeι_comp_hom i D e he
  have hcomp := hodgePullback_comp_overBase D.subschemeι X.obj.hom (D.subschemeι ≫ X.obj.hom)
    Y.obj.hom e.hom (subschemeι_square X.obj.hom D) we
    (by rw [Category.assoc]; exact we) p q x
  rw [hodgePullback_congr he Y.obj.hom X.obj.hom (𝟙 _) _ (hodgeSquare_w i)] at hcomp
  have hinj := (bijective_hodgePullback_of_isIso e.hom (D.subschemeι ≫ X.obj.hom) Y.obj.hom
    we p q).1
  exact hinj (hcomp.symm.trans (hx.trans (map_zero _).symm))

/-- Reindexing the cohomological degree of a Hodge class keeps the zero class. -/
theorem reindexHodgeDeg_zero {Z : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} Z.carrier}
    {φ : A ⟶ Z.sheaf} (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology Z.carrier) (SheafOfModules.moduleOfDifferentials.{u, u, u} φ))
    {p : ℕ} {q q' : ℤ} (hq : q = q') :
    AlgebraicGeometry.SheafOfModules.reindexHodgeDeg B (p := p) hq 0 = 0 := by
  subst hq
  rfl

/-- **Axiom (A4) for Hodge cohomology, in the algebra `H^*_{Hodge}(X/k)`, for a class dying
along the log poles**: if `c ∈ H^1(X, Ω^1_{X/k})` maps to zero in `H^1(X, Ω^1_{X/k}(log D))`
and `i^* a = 0`, then `a ∪ c = 0`. -/
theorem mul_hodgeClass_eq_zero_of_pull_eq_zero (i : Y ⟶ X)
    (D : ((toScheme k).obj X).IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (e : (toScheme k).obj Y ≅ D.subscheme) (he : e.hom ≫ D.subschemeι = (toScheme k).map i)
    (c : hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras X.obj.hom) 1 1)
    (hc : (cohomologyMap (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u}
        X.obj.hom.base).obj (Spec (.of k)).sheaf))
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (logPolesFormsBaseInclusion X.obj.hom D 1)) 1).hom (toHodgeComponentBase _ c) = 0)
    (a : hodgeAlgebraOf X) (ha : hodgePullbackOf i a = 0) :
    a * DirectSum.of (hodgePiece (formsAlgebras X.obj.hom)) 2
      (DirectSum.of (fun j : HodgeBidegreeInt 2 =>
        (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.1.1 (j.1.2 : ℤ) : Type u))
        bidegreeOneOne c) = 0 := by
  classical
  have hlog := hasLogPolesDeRhamComplex_of_divisor i D hD e he
  have hpiece : ∀ (n : ℤ) (x : hodgePiece (formsAlgebras X.obj.hom) n),
      hodgePiecePullback i.hom.left Y.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w i) n x = 0 →
      hodgePieceMul (formsAlgebras X.obj.hom) n 2 x
        (DirectSum.of (fun j : HodgeBidegreeInt 2 =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) j.1.1 (j.1.2 : ℤ) : Type u))
          bidegreeOneOne c) = 0 := by
    intro n x hx
    rw [← DirectSum.sum_support_of x, map_sum, AddMonoidHom.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hxj : hodgePullback i.hom.left Y.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w i) j.1.1
        (j.1.2 : ℤ) (x j) = 0 := by
      have := congrArg (fun z => z j) hx
      simpa [hodgePiecePullback, DirectSum.map_apply] using this
    refine (hodgePieceMul_of (formsAlgebras X.obj.hom) j bidegreeOneOne (x j) c).trans ?_
    have h0 := hodgeComponentCup_eq_zero_of_logPoles X.obj.hom D hD hlog j.1.1 (j.1.2 : ℤ) (x j)
      (hodgePullback_subschemeι_eq_zero i D e he j.1.1 (j.1.2 : ℤ) (x j) hxj) c hc
    have h2 : AlgebraicGeometry.SheafOfModules.hodgeCohomologyCup (formsAlgebras X.obj.hom)
        j.1.1 bidegreeOneOne.1.1 (j.1.2 : ℤ) (bidegreeOneOne.1.2 : ℤ) (x j) c = 0 := by
      show ((((j.1.2 : ℤ) * ((1 : ℕ) : ℤ)).negOnePow : ℤ)) •
        AlgebraicGeometry.SheafOfModules.hodgeComponentCup (formsAlgebras X.obj.hom)
          (AlgebraicGeometry.SheafOfModules.exteriorProductComponent (formsAlgebras X.obj.hom)
            j.1.1 1) (j.1.2 : ℤ) 1 (x j) c = 0
      rw [h0, smul_zero]
    refine (congrArg (fun z => DirectSum.of (fun k : HodgeBidegreeInt (n + 2) =>
        (hodgeCohomologyComponent (formsAlgebras X.obj.hom) k.1.1 (k.1.2 : ℤ) : Type u))
        ⟨(j.1.1 + bidegreeOneOne.1.1, j.1.2 + bidegreeOneOne.1.2),
          hodgeBidegreeInt_add j bidegreeOneOne⟩
        (AlgebraicGeometry.SheafOfModules.reindexHodgeDeg (formsAlgebras X.obj.hom)
          (Nat.cast_add j.1.2 bidegreeOneOne.1.2).symm z)) h2).trans ?_
    rw [reindexHodgeDeg_zero, map_zero]
  rw [← DirectSum.sum_support_of a, Finset.sum_mul]
  refine Finset.sum_eq_zero fun n _ => ?_
  have han : hodgePiecePullback i.hom.left Y.obj.hom X.obj.hom (𝟙 _) (hodgeSquare_w i) n
      (a n) = 0 := by
    have := congrArg (fun z => z n) ((hodgePullbackOf_eq_map i a).symm.trans ha)
    simpa [DirectSum.map_apply] using this
  rw [hodgeAlgebra_of_mul_of, hpiece n (a n) han, map_zero]

end Stacks.HodgeWeil

end
