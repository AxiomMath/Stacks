module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeQuasiDMExistence

/-!
# Stacks 0DU5 from the étale local chart

`EtaleLocalStructure.exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure`
proves **Stacks 0DU5** from two inputs: the étale local chart
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem` and the existence of residual
gerbes on quasi-DM algebraic stacks (**Stacks 06UI**). The second input is supplied here by
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM`, so that the étale local
chart is all that is left.

The theorem is not registered: the chart remains an explicit hypothesis. The registered proof of
Stacks 0DU5 does not go through
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem` at all; it runs the source's
proof on the quotient chart of Stacks 0DU3 directly, in
`StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureResidualGerbeChart`.

## Main results

* In the namespace `AlgebraicGeometry.Stack.EtaleLocalStructure`, the theorem
  `exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure` followed by
  `_of_hasQuasiDMPresentation`: Stacks 0DU5 from the étale local chart alone.

## References

* [Stacks Project, Tag 06UI](https://stacks.math.columbia.edu/tag/06UI)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.EtaleLocalStructure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0DU5 from the étale local chart.** Let `𝒳` be an algebraic stack which is quasi-DM
with separated diagonal, and let `x ∈ |𝒳|` be represented by a quasi-compact morphism from the
spectrum of a field. Granting the étale local chart
`AlgebraicGeometry.Stack.EtaleLocalStructure.LocalStructureTheorem`, there is a 1-morphism
`f : 𝒰 ⟶ 𝒳` of algebraic stacks with

1. a point `v ∈ |𝒰|` mapping to `x`, the residual gerbes of `𝒰` at `v` and of `𝒳` at `x`
   existing, and the 1-morphism between them induced by `f` being an isomorphism for every choice
   of them;
2. `f` representable by algebraic spaces and étale;
3. `𝒰` equivalent to `[U/R]` for a groupoid scheme `(U, R, s, t, c)` with `U` and `R` affine and
   `s` and `t` finite, flat and locally of finite presentation.

The residual gerbes exist by **Stacks 06UI**,
`AlgebraicGeometry.Stack.exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM`; the rest is
`exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure`. -/
theorem
  exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure_of_hasQuasiDMPresentation
    (hLS : LocalStructureTheorem.{u, w} B S hS hZ)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (hDM : AlgebraicStacks.IsAbsolutelyQuasiDM B S hS hZ 𝒳)
    (hSep : AlgebraicStacks.IsSeparated B S hS
      (relativeDiagonalAlgebraicStacks B S hS (structureMorphism B S hS 𝒳)))
    (x : AlgebraicStacks.points B S hS 𝒳)
    (hqc : ∃ p : FieldValuedPoint B S hS 𝒳.val.val,
      pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
        IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) :
    ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (f : 𝒰 ⟶ 𝒳) (v : AlgebraicStacks.points B S hS 𝒰)
      (G : Stacks.Groupoids.GroupoidScheme S) (hU : B.Contains G.objects.left)
      (hR : B.Contains G.arrows.left) (hP : B.Contains (pullback G.source G.target).left),
      AlgebraicStacks.pointsMap B S hS f v = x ∧
      (∃ P : ObjectProperty 𝒰.val.val.obj, IsResidualGerbeAt B S hS 𝒰 v P) ∧
      (∃ Q : ObjectProperty 𝒳.val.val.obj, IsResidualGerbeAt B S hS 𝒳 x Q) ∧
      (∀ (P : ObjectProperty 𝒰.val.val.obj) (Q : ObjectProperty 𝒳.val.val.obj)
        (hv : IsResidualGerbeAt B S hS 𝒰 v P)
        (hx : IsResidualGerbeAt B S hS 𝒳 (AlgebraicStacks.pointsMap B S hS f v) Q),
        Nonempty (Functor.IsEquivalenceOver
          (fullSubcategoryAlgebraicStack 𝒰 P hv.2.choose).val.val.p
          (fullSubcategoryAlgebraicStack 𝒳 Q hx.2.choose).val.val.p
          (CatFiberedInGroupoids.homFunctor
            (residualGerbeMap B S hS f hv.2.choose hx.2.choose
              (map_mem_of_isResidualGerbeAt B S hS f v _ rfl hv hx)).hom))) ∧
      IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
      IsEtale B S hS f ∧
      IsAffine G.objects.left ∧ IsAffine G.arrows.left ∧
      AlgebraicGeometry.IsFinite G.source.left ∧ AlgebraicGeometry.IsFinite G.target.left ∧
      Flat G.source.left ∧ Flat G.target.left ∧
      LocallyOfFinitePresentation G.source.left ∧ LocallyOfFinitePresentation G.target.left ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (quotientStack (G.realization B hS hU hR hP)).p 𝒰.val.val.p) :=
  exists_etale_affineGroupoid_neighborhood_residualGerbe_of_localStructure B S hS hZ hLS
    (fun 𝒴 h𝒴 y =>
      exists_isResidualGerbeAt_of_isAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒴 h𝒴 y)
    𝒳 hDM hSep x hqc

end AlgebraicGeometry.Stack.EtaleLocalStructure

end
