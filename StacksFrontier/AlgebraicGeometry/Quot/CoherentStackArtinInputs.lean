module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalizeEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTowerExistence
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackApproximation

/-!
# The inputs of Artin's criterion for `Coh_{X/Y}`, assembled

Stacks 09DS for a separated standing datum `f : X ⟶ Y` over an arbitrary base scheme, from the
inputs of Artin's criterion (Stacks 07Y4) over `Spec ℤ`, with the effectivity of formal objects
(Stacks 08W9, `AlgebraicGeometry.Space.CoherentSituation.isEffective_formalObject`) and the
effectivity of towers of square-zero thickenings
(`AlgebraicGeometry.Space.CoherentSituation.towerExistence_of_existence`, from Stacks 0CXB)
supplied. The remaining inputs are the representability of the diagonal (Stacks 08W6), the
finiteness of the tangent spaces (Stacks 08W8) and Grothendieck's existence theorem for
algebraic spaces (Stacks 0CXB).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_diagonal_tangent_existence`.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 08W9](https://stacks.math.columbia.edu/tag/08W9)
* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

attribute [local instance] pointTopology

/-- **Stacks 09DS from the representability of the diagonal (08W6), the finiteness of the tangent
spaces (08W8) and Grothendieck's existence theorem (0CXB).** For a separated finitely presented
morphism `f : X ⟶ Y` of algebraic spaces over any base scheme, `Coh_{X/Y}` is an algebraic stack,
given the representability of the diagonal of `Coh` over `Spec ℤ`, the finiteness of its tangent
spaces over coproducts of affine schemes of finite presentation over `Spec ℤ`, and Stacks 0CXB.
The effectivity of formal objects is Stacks 08W9 and the effectivity of square-zero towers comes
from Stacks 0CXB. -/
theorem isAlgebraicStack_of_diagonal_tangent_existence.{w} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
    (hsep : IsSeparated B S hS D.f.hom)
    (hdiag : ∀ D : CoherentSituation B (⊤_ Scheme.{u}) B.contains_terminal,
      Stack.HasRepresentableDiagonal B _ B.contains_terminal D.coherentCFG)
    (htangent : ∀ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal),
      LocallyOfFinitePresentation (B.inclusion.map V₀.hom) → IsCoproductOfAffines V₀ →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) B.contains_terminal),
        D₀.Y = (schemeSpaceFunctor B _ B.contains_terminal).obj V₀ →
        IsSeparated B _ B.contains_terminal D₀.f.hom →
        Stack.HasFiniteDimensionalTangentSpaces B _ B.contains_terminal D₀.coherentCFG)
    (h0CXB : ∀ s : InverseSystemExistenceSituation.{u},
      ∃ F : Modules.{u, u} s.B (limitBase s.system) s.containsLimitBase s.X.left.1 s.X.left.2,
          F.IsFinitePresentationOnSite ∧
            IsFlatOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2 s.X.hom.hom F ∧
            ∃ hcl : IsClosed (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                ((SheafOfModules.toSheaf _).obj F)),
              IsProperOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2
                (schemeSpace (limitBaseObject s.system s.B s.containsLimitBase)).2 s.X.hom.hom
                (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation s.B (limitBase s.system)
                  s.containsLimitBase s.finitePresentation.1)
                (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                  ((SheafOfModules.toSheaf _).obj F)) hcl ∧
              ∃ α : ∀ n : ℕ, (modulePullback s.B (limitBase s.system) s.containsLimitBase
                  (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).obj F ≅
                    (s.sheaf n).obj,
                ∀ n : ℕ,
                  (modulePullback s.B (limitBase s.system) s.containsLimitBase
                      (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).map
                        (α (n + 1)).hom ≫ (s.φ n).hom =
                    (modulePullbackCompIso s.B (limitBase s.system) s.containsLimitBase
                        (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)
                        (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X
                          (n + 1))).hom.app F ≫
                      eqToHom (congrArg (fun g => (modulePullback s.B (limitBase s.system)
                        s.containsLimitBase g).obj F)
                        (transitionSpace_spaceProjection s.system s.B s.containsLimitBase
                          s.containsBaseAt s.X n)) ≫
                      (α n).hom)
    :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val :=
  D.isAlgebraicStack_of_artinInputs_overIntegers hsep hdiag fun V₀ hV₀ hV₀c D₀ hY hsep₀ =>
    ⟨htangent V₀ hV₀ hV₀c D₀ hY hsep₀, fun ξ => D₀.isEffective_formalObject hsep₀ ξ,
      D₀.towerExistence_of_existence h0CXB hsep₀⟩

end AlgebraicGeometry.Space.CoherentSituation

end
