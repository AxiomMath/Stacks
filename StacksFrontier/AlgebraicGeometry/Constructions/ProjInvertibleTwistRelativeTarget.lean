module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeIntPowers
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeTrivialize
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeSections
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Segre
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Basis
public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The target of Tag 02NC's `θ`: `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` as a sheaf of graded algebras

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module,
`π : P = Proj_S(𝒜) ⟶ S`. Clause (1) of Tag 02NC asks for an isomorphism of `ℤ`-graded algebras onto
`⨁_{n ∈ ℤ} 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`. This file builds that graded algebra, as the degreewise tensor
product (`Stacks.AlgebraicGeometry.GradedAlgebraTwist.segre`) of the twists of `P` with the
pullback along `π` of the Laurent algebra `⨁_n ℒ^{⊗ n}`, and the restriction of a sheaf of graded
algebras along an open immersion.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.targetAlgebra`: **`⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.restrictAlgebra`: the restriction of a sheaf of
  graded algebras along an open immersion.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open Stacks.AlgebraicGeometry.ProjTwistSections AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

/-! ### Restriction of a sheaf of graded algebras along an open immersion -/

section Restrict

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (G : SchemeGradedAlgebra Y)

/-- **The restriction of a sheaf of graded algebras along an open immersion**: the pieces are the
restrictions, and the product of two sections over an open is their product over its image. -/
@[ega "II 8.14.6" "more general"]
def restrictAlgebra : SchemeGradedAlgebra X where
  piece n := Scheme.Modules.restrict (G.piece n) f
  mul i j :=
    { app := fun U => (G.mul i j).app (op (f ''ᵁ U.unop))
      map_smul_left := fun U r x y =>
        (G.mul i j).map_smul_left (op (f ''ᵁ U.unop)) ((f.appIso U.unop).inv r) x y
      map_smul_right := fun U r x y =>
        (G.mul i j).map_smul_right (op (f ''ᵁ U.unop)) ((f.appIso U.unop).inv r) x y
      naturality := fun {_U _V} h x y =>
        (G.mul i j).naturality (f.opensFunctor.map h.unop).op x y }
  one := ⟨fun U => G.one.eval (op (f ''ᵁ U.unop)),
    fun h => G.one.property (f.opensFunctor.map h.unop).op⟩
  mul_assoc i j k U x y z := G.mul_assoc i j k (op (f ''ᵁ U.unop)) x y z
  one_mul i U x := G.one_mul i (op (f ''ᵁ U.unop)) x
  mul_one i U x := G.mul_one i (op (f ''ᵁ U.unop)) x

/-- The piece of degree `n` of the restriction is the restriction of the piece of degree `n`. -/
@[simp] theorem restrictAlgebra_piece (n : ℤ) :
    (restrictAlgebra f G).piece n = Scheme.Modules.restrict (G.piece n) f := rfl

/-- The product of the restriction over `U` is the product of `G` over the image `f ''ᵁ U`. -/
theorem restrictAlgebra_mul_app (i j : ℤ) (U : X.Opens)
    (x : (G.piece i).val.obj (op (f ''ᵁ U))) (y : (G.piece j).val.obj (op (f ''ᵁ U))) :
    ((restrictAlgebra f G).mul i j).app (op U) x y = (G.mul i j).app (op (f ''ᵁ U)) x y := rfl

end Restrict

/-! ### The target algebra -/

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- The pullback along `π : Proj_S(𝒜) ⟶ S` of the Laurent algebra `⨁_n ℒ^{⊗ n}`. -/
abbrev pullbackLaurent : SchemeGradedAlgebra (relativeProj 𝒜).scheme :=
  Stacks.RingedSpace.pullbackGradedAlgebra (relativeProj 𝒜).toBase.toLRSHom.toShHom
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra S.sheaf.obj S.ringCatSheaf.property L)

/-- **The target of Tag 02NC's `θ`: the sheaf of `ℤ`-graded algebras
`⨁_{n ∈ ℤ} 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` on `P = Proj_S(𝒜)`**, the degreewise tensor product of the twists
of `P` with the pullback of the Laurent algebra of `ℒ`. -/
def targetAlgebra : SchemeGradedAlgebra (relativeProj 𝒜).scheme :=
  segre (O := (relativeProj 𝒜).scheme.sheaf.obj)
    (hO := (relativeProj 𝒜).scheme.ringCatSheaf.property)
    (Tag07ZGTwist.twistAlgebra 𝒜) (pullbackLaurent L 𝒜)

/-- The piece of degree `n` of the target is `𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`. -/
theorem targetAlgebra_piece (n : ℤ) :
    (targetAlgebra L 𝒜).piece n =
      tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n)) := rfl

/-- **The product of the target on pure tensors**: `(s ⊗ a)(t ⊗ b) = st ⊗ ab`. -/
theorem targetAlgebra_mul_gammaTmul (i j : ℤ) (U : (relativeProj 𝒜).scheme.Opens)
    (s : Γ(Tag07ZGTwist.relativeTwist 𝒜 i, U)) (a : ((pullbackLaurent L 𝒜).piece i).val.obj (op U))
    (t : Γ(Tag07ZGTwist.relativeTwist 𝒜 j, U))
    (b : ((pullbackLaurent L 𝒜).piece j).val.obj (op U)) :
    ((targetAlgebra L 𝒜).mul i j).app (op U)
        (gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 i)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L i)) U s a)
        (gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 j)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L j)) U t b) =
      gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 (i + j))
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L (i + j))) U
        (((Tag07ZGTwist.twistAlgebra 𝒜).mul i j).app (op U) s t)
        (((pullbackLaurent L 𝒜).mul i j).app (op U) a b) :=
  segre_mul_tensorSectionsAt (O := (relativeProj 𝒜).scheme.sheaf.obj)
    (hO := (relativeProj 𝒜).scheme.ringCatSheaf.property)
    (Tag07ZGTwist.twistAlgebra 𝒜) (pullbackLaurent L 𝒜) i j (op U) s a t b

/-! ### The target, transported to `Proj_S(ℬ)` -/

/-- **The target algebra, transported to `P' = Proj_S(ℬ)`** along the canonical isomorphism
`P' ≅ P` of Tag 02NC: its restriction along that isomorphism. -/
def transportedTarget : SchemeGradedAlgebra (relativeProj (twist 𝒜 L)).scheme :=
  restrictAlgebra (relativeTwistIso L 𝒜).hom (targetAlgebra L 𝒜)

/-- **The homogeneous-section map of the transported target**: the map labelled *multiply* in
clause (2) of Tag 02NC, `ℬ_k = 𝒜_k ⊗ ℒ^{⊗ k} ⟶ π_*(𝒪_P(k) ⊗ π^*ℒ^{⊗ k})`, carried to `P'`. -/
def transportedPsi (k : ℕ) :
    (twist 𝒜 L).piece (k : ℤ) ⟶
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).obj
        ((transportedTarget L 𝒜).piece (k : ℤ)) :=
  RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
      (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k) ≫
    (Scheme.Modules.pushforward (relativeProj 𝒜).toBase).map
      ((Scheme.Modules.restrictAdjunction (relativeTwistIso L 𝒜).hom).unit.app
        ((targetAlgebra L 𝒜).piece (k : ℤ))) ≫
    (Scheme.Modules.pushforwardComp (relativeTwistIso L 𝒜).hom (relativeProj 𝒜).toBase).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (relativeTwistIso_hom_comp_toBase L 𝒜)).hom.app _

/-- `transportedPsi` on sections: the *multiply* map, followed by a restriction map. -/
theorem transportedPsi_app (k : ℕ) (V : S.Opens)
    (h : (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ V) ≤
      (relativeProj 𝒜).toBase ⁻¹ᵁ V)
    (b : ((twist 𝒜 L).piece (k : ℤ)).val.obj (op V)) :
    (transportedPsi L 𝒜 k).val.app (op V) b =
      ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map (homOfLE h).op
        ((RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
          (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)).val.app (op V) b) := by
  exact PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece (k : ℤ)).val _ _ _ _

/-! ### The chart identification of the transported target, up to the absolute comparison -/

section Chart

variable (V : trivializingOpens L)

/-- The trivialization of `ℒ^{⊗ n}` over a member of the basis by the integer power of the chosen
section. -/
abbrev basisTriv (n : ℤ) :=
  intTrivIso L (basisSection_trivializesPower L V 1 Nat.one_pos) n

/-- **The chart identification of the transported target, before the absolute comparison**: the
restriction of `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`, transported to `P'`, along the chart of `P'` over a
member `V` of the basis, is the restriction along the comparison `Proj ℬ(V) ≅ Proj 𝒜(V)` of the
absolute twist `𝒪_{Proj 𝒜(V)}(n)`. It is the composite of the identifications of iterated
restrictions, the square `j'_V ≫ Φ = c_V ≫ j_V` of the glueing, the trivialization of the tensor
factor on the chart, and the chart identification of Tag 01NR for `𝒜`. -/
def chartPre (n : ℤ) :
    Scheme.Modules.restrict ((transportedTarget L 𝒜).piece n)
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1) ≅
      (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
        (twistingSheaf (𝒜.grading (V : S.Opens)) n) :=
  ((Scheme.Modules.restrictFunctorComp ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1)
      (relativeTwistIso L 𝒜).hom).app ((targetAlgebra L 𝒜).piece n)).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (chart_comp_relativeTwistIso_hom L 𝒜 V)).app
      ((targetAlgebra L 𝒜).piece n) ≪≫
    (Scheme.Modules.restrictFunctorComp (basisComparison L 𝒜 V)
      ((relativeProj 𝒜).chart (V : S.Opens) V.2.1)).app ((targetAlgebra L 𝒜).piece n) ≪≫
    (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).mapIso
      (chartTensorFactorIso 𝒜 V.2.1 n (tpMod L n) (basisTriv L V n)) ≪≫
    (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).mapIso
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso (V : S.Opens) V.2.1 n)

/-- The pullback along `π` of the integer power of the chosen section, a section of the pulled-back
Laurent algebra over the inverse image of `V`. -/
abbrev pullbackPow (n : ℤ) :
    ((pullbackLaurent L 𝒜).piece n).val.obj (op ((relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens))) :=
  Stacks.RingedSpace.pullbackUnit (relativeProj 𝒜).toBase.toLRSHom.toShHom (tpMod L n)
    (op (V : S.Opens)) (intPow L (basisSection_trivializesPower L V 1 Nat.one_pos) n)

/-- **The pulled-back powers multiply**: `π^*x^i · π^*x^j = π^*x^{i + j}`. -/
theorem pullbackPow_mul (i j : ℤ) :
    ((pullbackLaurent L 𝒜).mul i j).app (op ((relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens)))
        (pullbackPow L 𝒜 V i) (pullbackPow L 𝒜 V j) = pullbackPow L 𝒜 V (i + j) :=
  (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit
      (relativeProj 𝒜).toBase.toLRSHom.toShHom
      (Stacks.SheafOfModules.TensorPower.laurentAlgebra S.sheaf.obj S.ringCatSheaf.property L)
      i j (V : S.Opens) _ _).trans
    (congrArg (Stacks.RingedSpace.pullbackUnit (relativeProj 𝒜).toBase.toLRSHom.toShHom
      (tpMod L (i + j)) (op (V : S.Opens))) (lmul_intPow L _ i j))

/-- The trivialization of the tensor factor on the chart over a member of the basis. -/
abbrev chartTau (n : ℤ) := chartTensorFactorIso 𝒜 V.2.1 n (tpMod L n) (basisTriv L V n)

/-- The inverse of the trivialization of the tensor factor: tensoring with the pulled-back
power. -/
theorem chartTau_inv_app (n : ℤ) (U : (AlgebraicGeometry.Proj (𝒜.grading (V : S.Opens))).Opens)
    (s : Γ(Tag07ZGTwist.relativeTwist 𝒜 n, (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) :
    (chartTau L 𝒜 V n).inv.val.app (op U) s =
      gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))
        ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U) s
        (((pullbackLaurent L 𝒜).piece n).val.map
          (homOfLE (PullbackTrivialization.image_le_preimage (relativeProj 𝒜).toBase
            ((relativeProj 𝒜).chart (V : S.Opens) V.2.1)
            (chart_comp_toBase_preimage 𝒜 V.2.1) U)).op (pullbackPow L 𝒜 V n)) := by
  refine (chartTensorFactorIso_inv_app 𝒜 V.2.1 n (tpMod L n) (basisTriv L V n) U s).trans ?_
  refine congrArg (gammaTmul _ _ _ s) ?_
  refine congrArg (((pullbackLaurent L 𝒜).piece n).val.map _) ?_
  exact congrArg (Stacks.RingedSpace.pullbackUnit (relativeProj 𝒜).toBase.toLRSHom.toShHom
    (tpMod L n) (op (V : S.Opens))) (generator_intTrivIso L _ n)

/-- **The trivialization of the tensor factor is multiplicative**, in its inverse direction. -/
theorem chartTau_inv_mul (i j : ℤ) (U : (AlgebraicGeometry.Proj (𝒜.grading (V : S.Opens))).Opens)
    (s : Γ(Tag07ZGTwist.relativeTwist 𝒜 i, (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U))
    (t : Γ(Tag07ZGTwist.relativeTwist 𝒜 j, (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) :
    (chartTau L 𝒜 V (i + j)).inv.val.app (op U)
        (((Tag07ZGTwist.twistAlgebra 𝒜).mul i j).app
          (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) s t) =
      ((targetAlgebra L 𝒜).mul i j).app (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U))
        ((chartTau L 𝒜 V i).inv.val.app (op U) s) ((chartTau L 𝒜 V j).inv.val.app (op U) t) := by
  refine (chartTau_inv_app L 𝒜 V (i + j) U _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b => ((targetAlgebra L 𝒜).mul i j).app
    (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) a b)
    (chartTau_inv_app L 𝒜 V i U s).symm (chartTau_inv_app L 𝒜 V j U t).symm)
  refine Eq.trans ?_ (targetAlgebra_mul_gammaTmul L 𝒜 i j _ s _ t _).symm
  refine congrArg (gammaTmul _ _ _ _) ?_
  refine Eq.trans ?_ (((pullbackLaurent L 𝒜).mul i j).naturality _ _ _)
  exact congrArg _ (pullbackPow_mul L 𝒜 V i j).symm

/-- The image under the chart of `P'` and the canonical isomorphism is the image under the
comparison and the chart of `P`. -/
theorem image_chart_relativeTwistIso (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading
      (V : S.Opens))).Opens) :
    (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W) =
      (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ (basisComparison L 𝒜 V ''ᵁ W) := by
  simp only [← Scheme.Hom.comp_image, chart_comp_relativeTwistIso_hom L 𝒜 V]

/-- **`chartPre` on sections**: a restriction map between two equal opens, then the
trivialization of the tensor factor, then the chart identification of Tag 01NR for `𝒜`. -/
theorem chartPre_hom_app (n : ℤ)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (x : (Scheme.Modules.restrict ((transportedTarget L 𝒜).piece n)
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1)).val.obj (op W)) :
    (chartPre L 𝒜 V n).hom.val.app (op W) x =
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso (V : S.Opens)
          V.2.1 n).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W))
        ((chartTau L 𝒜 V n).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W))
          (((targetAlgebra L 𝒜).piece n).val.map
            (homOfLE (image_chart_relativeTwistIso L 𝒜 V W).ge).op x)) := by
  simp only [chartPre]
  refine congrArg (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso
    (V : S.Opens) V.2.1 n).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W))) ?_
  refine congrArg ((chartTau L 𝒜 V n).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W))) ?_
  have h1 : ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ≫
      (relativeTwistIso L 𝒜).hom) ''ᵁ W ≤ (relativeTwistIso L 𝒜).hom ''ᵁ
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W) :=
    (Scheme.Hom.comp_image _ _ W).le
  have h2 : (basisComparison L 𝒜 V ≫ (relativeProj 𝒜).chart (V : S.Opens) V.2.1) ''ᵁ W ≤
      ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ≫
        (relativeTwistIso L 𝒜).hom) ''ᵁ W := by
    rw [Scheme.Hom.comp_image, Scheme.Hom.comp_image]
    exact (image_chart_relativeTwistIso L 𝒜 V W).ge
  have h3 : (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ (basisComparison L 𝒜 V ''ᵁ W) ≤
      (basisComparison L 𝒜 V ≫ (relativeProj 𝒜).chart (V : S.Opens) V.2.1) ''ᵁ W :=
    (Scheme.Hom.comp_image _ _ W).ge
  show ((targetAlgebra L 𝒜).piece n).val.map (homOfLE h3).op
      (((targetAlgebra L 𝒜).piece n).val.map (homOfLE h2).op
        (((targetAlgebra L 𝒜).piece n).val.map (homOfLE h1).op x)) = _
  exact (congrArg (((targetAlgebra L 𝒜).piece n).val.map (homOfLE h3).op)
    (PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece n).val (homOfLE h1).op
      (homOfLE h2).op (homOfLE (h2.trans h1)).op x)).trans
    (PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece n).val
      (homOfLE (h2.trans h1)).op (homOfLE h3).op _ x)

/-- **The trivialization of the tensor factor is multiplicative.** -/
theorem chartTau_hom_mul (i j : ℤ) (U : (AlgebraicGeometry.Proj (𝒜.grading (V : S.Opens))).Opens)
    (a : ((targetAlgebra L 𝒜).piece i).val.obj
      (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)))
    (b : ((targetAlgebra L 𝒜).piece j).val.obj
      (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U))) :
    (chartTau L 𝒜 V (i + j)).hom.val.app (op U)
        (((targetAlgebra L 𝒜).mul i j).app
          (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) a b) =
      ((Tag07ZGTwist.twistAlgebra 𝒜).mul i j).app
        (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U))
        ((chartTau L 𝒜 V i).hom.val.app (op U) a) ((chartTau L 𝒜 V j).hom.val.app (op U) b) := by
  have h' : ((targetAlgebra L 𝒜).mul i j).app
      (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) a b =
      (chartTau L 𝒜 V (i + j)).inv.val.app (op U)
        (((Tag07ZGTwist.twistAlgebra 𝒜).mul i j).app
          (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U))
          ((chartTau L 𝒜 V i).hom.val.app (op U) a) ((chartTau L 𝒜 V j).hom.val.app (op U) b)) :=
    (congrArg₂ (fun a' b' => ((targetAlgebra L 𝒜).mul i j).app
      (op ((relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ U)) a' b')
      (TwistRigidity.iso_inv_app_hom_app (chartTau L 𝒜 V i) (op U) a).symm
      (TwistRigidity.iso_inv_app_hom_app (chartTau L 𝒜 V j) (op U) b).symm).trans
      (chartTau_inv_mul L 𝒜 V i j U _ _).symm
  exact (congrArg ((chartTau L 𝒜 V (i + j)).hom.val.app (op U)) h').trans
    (TwistRigidity.iso_hom_app_inv_app (chartTau L 𝒜 V (i + j)) (op U) _)

/-- **`chartPre` carries the product of the transported target to the canonical product of the
absolute twists.** -/
theorem chartPre_hom_mul (i j : ℤ)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (x : ((transportedTarget L 𝒜).piece i).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W)))
    (y : ((transportedTarget L 𝒜).piece j).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W))) :
    (chartPre L 𝒜 V (i + j)).hom.val.app (op W)
        (((transportedTarget L 𝒜).mul i j).app
          (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W)) x y) =
      absoluteTwistProduct (𝒜.grading (V : S.Opens)) i j (basisComparison L 𝒜 V ''ᵁ W)
        ((chartPre L 𝒜 V i).hom.val.app (op W) x) ((chartPre L 𝒜 V j).hom.val.app (op W) y) := by
  refine (chartPre_hom_app L 𝒜 V (i + j) W _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (absoluteTwistProduct (𝒜.grading (V : S.Opens)) i j
    (basisComparison L 𝒜 V ''ᵁ W)) (chartPre_hom_app L 𝒜 V i W x).symm
    (chartPre_hom_app L 𝒜 V j W y).symm)
  refine Eq.trans (congrArg (fun z =>
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso (V : S.Opens) V.2.1
        (i + j)).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W))
        ((chartTau L 𝒜 V (i + j)).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W)) z))
    (((targetAlgebra L 𝒜).mul i j).naturality
      (homOfLE (image_chart_relativeTwistIso L 𝒜 V W).ge).op x y)) ?_
  refine Eq.trans (congrArg (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso
      (V : S.Opens) V.2.1 (i + j)).hom.val.app (op (basisComparison L 𝒜 V ''ᵁ W)))
    (chartTau_hom_mul L 𝒜 V i j (basisComparison L 𝒜 V ''ᵁ W) _ _)) ?_
  exact (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := Set.univ)
    (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜)).chartIso_hom_mul (V : S.Opens) V.2.1
      (Set.mem_univ _) i j (basisComparison L 𝒜 V ''ᵁ W) _ _

end Chart

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
