module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedCommutative
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Restrict
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose

/-!
# Restricting Situation 01NN's graded algebra to an open

Let `S` be a scheme and `A` a quasi-coherent graded `𝒪_S`-algebra in the sheaf-theoretic form of
Situation 01NN. For a morphism `g : X ⟶ S` the inverse image `g^*A` is again such an algebra,
and as a sheaf of graded algebras it is the base-changed algebra `baseAlgebra g A`. For an open
immersion `f : X ⟶ S` the inverse image `f^*A` is isomorphic, as a sheaf of graded algebras, to
the restriction `A|_X`, whose sections over `V` are the sections of `A` over `f ''ᵁ V`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.pullback`: the inverse image of
  `A` along a morphism of base schemes, as graded algebra data of Situation 01NN.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictPullbackPieceIso`: the isomorphism
  `A|_X ≅ f^*A` in each degree.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictUnitalHom`: the unit of the
  restriction adjunction as a homomorphism of sheaves of graded algebras `A ⟶ f_*(A|_X)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictPullbackUnitalHom`: the homomorphism of
  sheaves of graded algebras `f^*A ⟶ A|_X`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra_pullback`:
  `situationAlgebra (A.pullback g) = baseAlgebra g (situationAlgebra A)`.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.restrictPullbackUnitalHom_app` and
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.isIso_restrictPullbackUnitalHom_app`: in each
  degree `f^*A ⟶ A|_X` is the inverse of the canonical isomorphism
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so it is an isomorphism.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra (IsCommutative VanishesInNegativeDegrees
  toSheafGradedAlgebra)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S X T : Scheme.{u}}

/-- A local section of a zero object of `X.Modules` vanishes. -/
theorem section_eq_zero_of_isZero {M : X.Modules} (h : IsZero M) (V : X.Opens) (x : Γ(M, V)) :
    x = 0 :=
  (ModuleCat.subsingleton_of_isZero
    ((PresheafOfModules.evaluation _ (op V)).map_isZero
      ((SheafOfModules.forget _).map_isZero h))).allEq x 0

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S X : Scheme.{u}} (A : SheafGradedAlgebra S) (g : X ⟶ S)

/-- The inverse image of Situation 01NN's graded algebra along a morphism `g` of base schemes, as
graded algebra data of Situation 01NN: its pieces are the inverse images of the pieces, with the
multiplication and unit of `Stacks.RingedSpace.pullbackGradedAlgebra`. -/
def pullback : SheafGradedAlgebra X :=
  toSheafGradedAlgebra (Stacks.Conormal.gradedPullback g (situationAlgebra A))
    (fun i j U a b =>
      Stacks.RingedSpace.pullbackGradedAlgebra_mul_comm (ringedSpaceHom g) (situationAlgebra A)
        (fun i' j' V c d => A.mul_comm i' j' V.unop c d) i j U a b)
    (fun n hn U x =>
      section_eq_zero_of_isZero
        (Stacks.Conormal.gradedPullback_isZero g (situationAlgebra A)
          (A.negative_isZero n hn)) U.unop x)
    (fun n =>
      Stacks.Conormal.gradedPullback_isQuasicoherent g (situationAlgebra A)
        (fun m => A.isQuasicoherent m) n)

@[simp] theorem pullback_piece (n : ℤ) :
    (A.pullback g).piece n = (Scheme.Modules.pullback g).obj (A.piece n) := rfl

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S X T : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- The inverse image of Situation 01NN's graded algebra, as a sheaf of graded algebras, is the
base-changed algebra `baseAlgebra g`. -/
theorem situationAlgebra_pullback (g : X ⟶ S) :
    situationAlgebra (A.pullback g) = baseAlgebra g (situationAlgebra A) := rfl

/-! ### The comparison of the two spellings -/

/-- For an open immersion `f`, the degree-`n` piece of the restriction `A|_X` is isomorphic to the
degree-`n` piece of the inverse image `f^*A`. -/
def restrictPullbackPieceIso (f : X ⟶ S) [IsOpenImmersion f] (n : ℤ) :
    (A.restrict f).piece n ≅ (A.pullback f).piece n :=
  (Scheme.Modules.restrictFunctorIsoPullback f).app (A.piece n)

/-! ### The comparison is a homomorphism of graded algebras -/

/-- The unit of the restriction adjunction, as a homomorphism of sheaves of graded algebras
`A ⟶ f_*(A|_X)`. -/
def restrictUnitalHom (f : X ⟶ S) [IsOpenImmersion f] :
    SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A)
      (Stacks.RingedSpace.pushforwardAlgebra (ringedSpaceHom f)
        (situationAlgebra (A.restrict f))) where
  app n := (Scheme.Modules.restrictAdjunction f).unit.app (A.piece n)
  map_mul i j W x y := (A.mul i j).naturality (f.image_preimage_le W.unop) x y
  map_one W := A.one_res (f.image_preimage_le W.unop)

/-- The homomorphism of sheaves of graded algebras `f^*A ⟶ A|_X` adjoint to `restrictUnitalHom`
under `f^* ⊣ f_*`. -/
def restrictPullbackUnitalHom (f : X ⟶ S) [IsOpenImmersion f] :
    SheafOfModules.GradedAlgebra.UnitalHom (baseAlgebra f (situationAlgebra A))
      (situationAlgebra (A.restrict f)) :=
  Stacks.RingedSpace.transposeUnitalHom (ringedSpaceHom f) (restrictUnitalHom A f)

/-- In each degree, `restrictPullbackUnitalHom` is the inverse of the canonical isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem restrictPullbackUnitalHom_app (f : X ⟶ S) [IsOpenImmersion f] (n : ℤ) :
    (restrictPullbackUnitalHom A f).app n =
      (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (A.piece n) := by
  have hdef : (Scheme.Modules.restrictFunctorIsoPullback f).inv.app (A.piece n) =
      (Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.restrictAdjunction f)).hom.app (A.piece n) :=
    Adjunction.leftAdjointUniq_inv_app _ _ _
  have key := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.restrictAdjunction f)
    (A.piece n)
  symm
  rw [hdef, show (restrictPullbackUnitalHom A f).app n =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv (A.piece n)
        (Scheme.Modules.restrict (A.piece n) f)).symm
        ((Scheme.Modules.restrictAdjunction f).unit.app (A.piece n)) from rfl,
    ← key, Equiv.symm_apply_apply]

/-- Every degreewise component of `restrictPullbackUnitalHom` is an isomorphism. -/
theorem isIso_restrictPullbackUnitalHom_app (f : X ⟶ S) [IsOpenImmersion f] (n : ℤ) :
    IsIso ((restrictPullbackUnitalHom A f).app n) := by
  have h : IsIso ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app (A.piece n)) :=
    inferInstance
  rw [restrictPullbackUnitalHom_app]
  exact h

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
