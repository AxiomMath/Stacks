module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.OverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeronese

/-!
# The datum of Tag 01O8 from a homomorphism of graded algebras

A homomorphism of graded algebras `ψ : f^*𝒜 ⟶ ⨁_{n} ℒ^{⊗ n}` gives the datum of
[Stacks, Tag 01O8]: its components in adjoint form, their values on sections and their
multiplicativity.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L)

/-- The degree identification `n = n · 1` on the pieces of `𝒜`. -/
def pieceCast (n : ℤ) : (situationAlgebra A).piece n ⟶ (situationAlgebra A).piece (n * 1) :=
  eqToHom (congrArg (situationAlgebra A).piece (mul_one n).symm)

/-- `ℒ^{⊗ n}`, the iterated tensor power, as a sheaf of modules on the ringed space of `T`. -/
abbrev natPowRS (n : ℕ) : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  natTensorPow (C := T.Modules) L n

/-- **The component `f^*𝒜_n ⟶ ℒ^{⊗ n}` of `ψ`**, read on the iterated tensor power. -/
def degreeComponent (n : ℕ) :
    (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece (n : ℤ)) ⟶
      natPowRS (L := L) n :=
  (pullbackFunctor (ringedSpaceHom f)).map (pieceCast (A := A) (n : ℤ)) ≫ ψ.app (n : ℤ) ≫
    (show (laurent L).piece (n : ℤ) ⟶ natPowRS (L := L) n from (powCompare L n).inv)

/-- The component in adjoint form, as a morphism into the direct image. -/
def adjComponent (n : ℕ) :
    (situationAlgebra A).piece (n : ℤ) ⟶
      (pushforwardFunctor (ringedSpaceHom f)).obj (natPowRS (L := L) n) :=
  (pullbackAdjunction (ringedSpaceHom f)).homEquiv _ _ (degreeComponent ψ n)

/-- **The value `ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ n})` of `ψ` on a homogeneous section `a` of degree
`n` over `V`**: the pullback of `a` pushed through the degree-`n` component of `ψ`, read on the
iterated tensor power. -/
def valueSec (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) : Γ(natTensorPow L n, f ⁻¹ᵁ V) :=
  (powCompare L n).inv.app (f ⁻¹ᵁ V)
    (ψ.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a))

/-- On a section `a` of `𝒜_n` over `V`, the degree-`n` component of `ψ` in adjoint form takes the
value `valueSec ψ n V a`. -/
theorem adjComponent_app (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    PresheafOfModules.Hom.app (adjComponent ψ n).val (op V) a = valueSec ψ n V a := by
  have h1 := homEquiv_val_app (ringedSpaceHom f) _ _ (degreeComponent ψ n) (op V) a
  have h2 := pullbackUnit_naturality (ringedSpaceHom f) (pieceCast (A := A) (n : ℤ)) (op V) a
  rw [adjComponent, h1]
  show (powCompare L n).inv.app (f ⁻¹ᵁ V) (PresheafOfModules.Hom.app (ψ.app (n : ℤ)).val _
      (PresheafOfModules.Hom.app
        ((pullbackFunctor (ringedSpaceHom f)).map (pieceCast (A := A) (n : ℤ))).val _
        (pullbackUnit (ringedSpaceHom f) ((situationAlgebra A).piece (n : ℤ)) (op V) a))) = _
  exact congrArg (fun z => (powCompare L n).inv.app (f ⁻¹ᵁ V)
    ((ψ.app (n : ℤ)).val.app
      ((RingedSpaceModuleAdjunction.opensMap (ringedSpaceHom f)).op.obj (op V)) z)) h2

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- Composing two transports along equalities of degrees. -/
theorem eqToHom_eqToHom_app {i j k : ℤ} (p : i = j) (q : j = k) (V : S.Opens)
    (x : Γ(A.piece i, V)) :
    (eqToHom (congrArg A.piece q)).val.app (op V) ((eqToHom (congrArg A.piece p)).val.app (op V) x)
      = (eqToHom (congrArg A.piece (p.trans q))).val.app (op V) x := by
  subst p q
  rfl

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- Moving a homogeneous product along equalities of degrees. -/
theorem eqToHom_mul_app {i j i' j' : ℤ} (hi : i = i') (hj : j = j') (h : i + j = i' + j')
    (V : S.Opens) (a : Γ(A.piece i, V)) (b : Γ(A.piece j, V)) :
    (eqToHom (congrArg A.piece h)).val.app (op V) ((A.mul i j).app V a b)
      = (A.mul i' j').app V ((eqToHom (congrArg A.piece hi)).val.app (op V) a)
          ((eqToHom (congrArg A.piece hj)).val.app (op V) b) := by
  subst hi hj
  rfl

/-- **`ψ` is multiplicative across degrees, on values.** -/
theorem valueSec_mul (n m : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V))
    (b : Γ(A.piece (m : ℤ), V)) :
    valueSec ψ (n + m) V ((A.mul (n : ℤ) (m : ℤ)).app V a b)
      = Stacks.AlgebraicGeometry.NatTensorPowLocalMul.localMulSections L
          (valueSec ψ n V a) (valueSec ψ m V b) := by
  have hc : (pieceCast (A := A) ((n : ℤ) + (m : ℤ))).val.app (op V)
        ((A.mul (n : ℤ) (m : ℤ)).app V a b)
      = (eqToHom (congrArg A.piece
            (by ring : (n : ℤ) * 1 + (m : ℤ) * 1 = ((n : ℤ) + (m : ℤ)) * 1))).val.app
          (op V) ((A.mul ((n : ℤ) * 1) ((m : ℤ) * 1)).app V
            ((pieceCast (A := A) (n : ℤ)).val.app (op V) a)
            ((pieceCast (A := A) (m : ℤ)).val.app (op V) b)) :=
    (eqToHom_eqToHom_app (A := A) (by ring : (n : ℤ) + (m : ℤ) = (n : ℤ) * 1 + (m : ℤ) * 1)
      (by ring) V _).symm.trans
      (congrArg (fun z => (eqToHom (congrArg A.piece
          (by ring : (n : ℤ) * 1 + (m : ℤ) * 1 = ((n : ℤ) + (m : ℤ)) * 1))).val.app (op V) z)
        (eqToHom_mul_app (A := A) (mul_one (n : ℤ)).symm (mul_one (m : ℤ)).symm (by ring) V a b))
  have hmul := ψ.sectionHom_mul (n : ℤ) (m : ℤ) (op V)
    ((pieceCast (A := A) (n : ℤ)).val.app (op V) a) ((pieceCast (A := A) (m : ℤ)).val.app (op V) b)
  have e1 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (powCompare L n) (f ⁻¹ᵁ V)
    (ψ.sectionHom (n : ℤ) (op V) ((pieceCast (A := A) (n : ℤ)).val.app (op V) a))
  have e2 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (powCompare L m) (f ⁻¹ᵁ V)
    (ψ.sectionHom (m : ℤ) (op V) ((pieceCast (A := A) (m : ℤ)).val.app (op V) b))
  refine Eq.trans ?_ (congrArg₂
    (fun (x : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (n : ℤ), f ⁻¹ᵁ V))
        (y : Γ(Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ), f ⁻¹ᵁ V)) =>
      (powCompare L (n + m)).inv.app (f ⁻¹ᵁ V) (Stacks.TensorPowerDivision.localMul L x y))
    e1 e2).symm
  refine Eq.trans ?_ (congrArg (fun z => (powCompare L (n + m)).inv.app (f ⁻¹ᵁ V) z) hmul.symm)
  exact congrArg (fun z => (powCompare L (n + m)).inv.app (f ⁻¹ᵁ V)
    (ψ.sectionHom ((n : ℤ) + (m : ℤ)) (op V) z)) hc

/-- **The datum of [Stacks, Tag 01O8] attached to a homomorphism of graded algebras
`ψ : f^*𝒜 ⟶ ⨁_{n} ℒ^{⊗ n}`**: its components, in adjoint form. -/
def toGradedPowerMap : GradedPowerMap A f where
  L := L
  invertible := inferInstance
  ψ n := adjComponent ψ n
  map_mul n m V a b := by
    have h1 := adjComponent_app ψ (n + m) V ((A.mul (n : ℤ) (m : ℤ)).app V a b)
    have h2 := adjComponent_app ψ n V a
    have h3 := adjComponent_app ψ m V b
    exact h1.trans ((valueSec_mul ψ n m V a b).trans (by rw [← h2, ← h3]; rfl))

/-- The values of the datum attached to `ψ` are `valueSec`. -/
theorem toGradedPowerMap_value (n : ℕ) (V : S.Opens) (a : Γ(A.piece (n : ℤ), V)) :
    (toGradedPowerMap ψ).value n V a = valueSec ψ n V a :=
  adjComponent_app ψ n V a

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
