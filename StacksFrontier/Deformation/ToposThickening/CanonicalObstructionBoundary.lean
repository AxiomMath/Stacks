module

public import StacksFrontier.CategoryTheory.Triangulated.ConnectingClassComparison
public import StacksFrontier.Deformation.ToposThickening.CanonicalCotangentObstruction

/-!
# The obstruction class of Tag 08V5 as a boundary

Let `S` be a square-zero extension problem of ringed topoi (Tag 08UF). Write `f⁻¹O_{B'}` for the
inverse image of the thickened base, `f⁻¹O_B` for that of the reduced base, and `G` for the target
module of `S`. Let `0 → G → G₂ → G₁ → 0` be a short exact sequence of `O`-modules. Take classes

* `e₂ : L_{O/f⁻¹O_{B'}} ⟶ G₂[1]`, whose restriction along the first map `a` of the fundamental
  triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O` is the class `γ` of `S` pushed into `G₂`, and
* `e₁ : L_{O/f⁻¹O_B} ⟶ G₁[1]`, whose pullback along the second map `b` of that triangle is `e₂`
  pushed into `G₁`.

Then the obstruction class `o(S) = −(δ.comp γ)` of Tag 08V5, on the named connecting morphism, is
the image of `e₁` under the connecting map `Ext¹(L, G₁) ⟶ Ext²(L, G)` of the short exact
sequence. In the deformation theory of an algebraic space over a short exact sequence of
thickenings `A₃' → A₂' → A₁'` of `A`:

* `S` is the problem of `A₃'`;
* `e₂` is the class of a lift over `A₂'`, read over `A₃'`;
* `e₁` is the tangent class of its restriction to `A₁' = A[I₁]`.

Under those identifications the statement is condition (iv) of [Stacks, Tag 07YY]: the
space-level form of [Stacks, Tag 08VY], with the cotangent complex.

## Main results

* `RingedToposExtensionProblem.canonicalObstructionClass_eq_comp_singleδ`: the obstruction class
  of Tag 08V5 is the boundary of a tangent class.

## References

* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

omit [HasWeakSheafify X.J CommRingCat.{u}] in
/-- **The obstruction class of Tag 08V5 is the boundary of a tangent class.** Let
`0 → G → G₂ → G₁ → 0` be a short exact sequence of `O`-modules starting at the target module `G`
of `S`. Suppose `e₂ : L_{O/f⁻¹O_{B'}} ⟶ G₂[1]` restricts along the first map of the fundamental
triangle to the class `γ` of `S` pushed into `G₂`. Suppose `e₁ : L_{O/f⁻¹O_B} ⟶ G₁[1]` pulls back
along the second map to `e₂` pushed into `G₁`. Then `o(S)` is the image of `e₁` under the
connecting map of the short exact sequence. -/
public theorem canonicalObstructionClass_eq_comp_singleδ
    {G₂ G₁ : Sheaf.targetModules.{u, u, u} X.J X.O} (i : targetG.{u, u, u} S ⟶ G₂)
    (π : G₂ ⟶ G₁) (hzero : i ≫ π = 0) (hSq : (ShortComplex.mk i π hzero).ShortExact)
    (e₂ : DerivedCategory.Q.obj (Sheaf.cotangentComplex.{u, u, u} X.J
        (S.baseReductionInverseImage ≫ S.f.fSharpInverseImage)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G₂)⟦(1 : ℤ)⟧)
    (e₁ : Sheaf.cotangentComplexDerived.{u, u, u, t} X.J S.f.fSharpInverseImage ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G₁)⟦(1 : ℤ)⟧)
    (h₁ : DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage) ≫ e₂ =
        S.obstructionBaseClass ≫ ((DerivedCategory.singleFunctor _ 0).map i)⟦(1 : ℤ)⟧')
    (h₂ : DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage) ≫ e₁ =
        e₂ ≫ ((DerivedCategory.singleFunctor _ 0).map π)⟦(1 : ℤ)⟧') :
    S.canonicalObstructionClass =
      ShiftedHom.comp (a := (1 : ℤ)) e₁ hSq.singleδ (show (1 : ℤ) + 1 = 2 by norm_num) :=
  DerivedCategory.neg_shiftedHom_comp_eq_comp_singleδ _
    S.canonicalTowerConnecting_distinguished hSq
    (hP := Sheaf.isLE_Q_obj_baseChangedCotangentComplex.{u, u, u} X.J
      S.baseReductionInverseImage S.f.fSharpInverseImage)
    S.obstructionBaseClass e₂ e₁ h₁ h₂

end Deformation.ToposThickening.RingedToposExtensionProblem

end
