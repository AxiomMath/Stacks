module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.WedgeLinear
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProductLinear

/-!
# Rescaling the trace of relative Poincaré duality by a unit

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) let
`t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` have the property of [Stacks, Tag 0G8I]: all the pairings
`Rf_*Ω^p ⊗^L Rf_*Ω^{n-p}[n] ⟶ 𝒪_S` given by the relative cup product composed with `t` are
perfect. Precomposing `t` with multiplication by a global function `g ∈ Γ(X, 𝒪_X)` precomposes
each of these pairings with multiplication by `g` on its first factor. Hence for a unit `g` the
rescaled trace has the property again, and conversely every `t'` with the property is obtained
from `t` this way.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeHodgePairing_formsShiftSMul`: the pairing of the
  rescaled trace.
* `AlgebraicGeometry.RelativeDualitySituation.IsRelativePoincareTrace.formsShiftSMul`: rescaling
  by a unit preserves the property.
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Rescaling the trace rescales the pairing**: the pairing determined by `g · t` is the pairing
determined by `t` precomposed with multiplication by `g` on its first factor. -/
theorem relativeHodgePairing_formsShiftSMul (n p q : ℤ) (h : p + q = n) (g : Γ(X, ⊤))
    (t : (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    f.relativeHodgePairing n p q h (f.formsShiftSMul n g ≫ t) =
      ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).map
          ((Stacks.Duality.derivedPushforward f).map (f.formsInDegreeZeroSMul g p))).app _ ≫
        f.relativeHodgePairing n p q h t := by
  have hw := congrArg (Stacks.Duality.derivedPushforward f).map
    (formsDerivedWedgeShift_smul_left f g n p q n h)
  have hc := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural_left
    f.toLRSHom.toShHom (f.formsInDegreeZeroSMul g p) ((formsInDegreeZero f q)⟦n⟧)
  refine Eq.symm ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans (hw.trans
        (Functor.map_comp _ _ _)))).trans (Category.assoc _ _ _)))))))

/-- Multiplication by a unit of `Γ(X, 𝒪_X)` on `Ω^a_{X/S}` in degree zero is an isomorphism. -/
theorem isIso_formsInDegreeZeroSMul (g : (Γ(X, ⊤))ˣ) (a : ℤ) :
    IsIso (f.formsInDegreeZeroSMul (g : Γ(X, ⊤)) a) := by
  have e : ∀ s t : Γ(X, ⊤), t * s = 1 →
      f.formsInDegreeZeroSMul s a ≫ f.formsInDegreeZeroSMul t a = 𝟙 _ := fun s t hts =>
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map_comp _ _).symm.trans
        ((congrArg (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
          ((Stacks.Cohomology.InvertibleDerived.smulHom_comp (X := X.toRingedSpace) s t _).trans
            ((congrArg (fun r => Stacks.Cohomology.InvertibleDerived.smulHom
              (X := X.toRingedSpace) r (relativeDifferentialForms f a)) hts).trans
              (AlgebraicGeometry.SheafOfModules.smulHom_one _)))).trans
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map_id _)))).trans
      (DerivedCategory.Q.map_id _))
  exact ⟨f.formsInDegreeZeroSMul ((g⁻¹ : (Γ(X, ⊤))ˣ) : Γ(X, ⊤)) a,
    e _ _ (Units.inv_mul g), e _ _ (Units.mul_inv g)⟩

end Scheme.Hom

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Rescaling the trace by a unit preserves perfect pairings**, for any tensor–internal-Hom
adjunction `DY`: precomposing the pairing with multiplication by a unit on its first factor
precomposes the map it determines with an isomorphism. -/
theorem isPerfectDerivedPairing_relativeHodgePairing_formsShiftSMul
    (DY : DerivedTensorHomAdjunction S) (n p q : ℤ) (h : p + q = n) (g : (Γ(X, ⊤))ˣ)
    (t : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj)
    (ht : IsPerfectDerivedPairing DY (f.relativeHodgePairing n p q h t)) :
    IsPerfectDerivedPairing DY
      (f.relativeHodgePairing n p q h (f.formsShiftSMul n (g : Γ(X, ⊤)) ≫ t)) := by
  obtain ⟨h₁, h₂, h₃⟩ := ht
  refine ⟨h₁, h₂, ?_⟩
  have := f.isIso_formsInDegreeZeroSMul g p
  have hv : IsIso ((Stacks.Duality.derivedPushforward f).map
      (f.formsInDegreeZeroSMul (g : Γ(X, ⊤)) p)) := Functor.map_isIso _ _
  have e := DY.homEquiv_symm_map_app_comp
    ((Stacks.Duality.derivedPushforward f).map (f.formsInDegreeZeroSMul (g : Γ(X, ⊤)) p))
    (f.relativeHodgePairing n p q h t)
  rw [relativeHodgePairing_formsShiftSMul, e]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hv h₃

end Scheme.Hom

namespace RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **Rescaling a trace by a unit gives a trace**: if `t` has the property of
[Stacks, Tag 0G8I], so does `t` precomposed with multiplication by a unit of `Γ(X, 𝒪_X)`. -/
theorem IsRelativePoincareTrace.formsShiftSMul {D : RelativeDualitySituation.{u}}
    {t : (Stacks.Duality.derivedPushforward D.f).obj ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj}
    (ht : D.IsRelativePoincareTrace t) (g : (Γ(D.X, ⊤))ˣ) :
    D.IsRelativePoincareTrace (D.f.formsShiftSMul D.n (g : Γ(D.X, ⊤)) ≫ t) :=
  fun p =>
    D.f.isPerfectDerivedPairing_relativeHodgePairing_formsShiftSMul _ D.n p (D.n - p) _ g t (ht p)

end RelativeDualitySituation

end AlgebraicGeometry

end
