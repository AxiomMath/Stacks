module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinInputsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable

/-!
# The stack of coherent sheaves is algebraic, given Grothendieck's existence theorem

For a separated morphism `f : X ⟶ Y` of finite presentation of algebraic spaces over a scheme `S`,
`Coh_{X/Y}` is an algebraic stack over `S` (Stacks 09DS), granted Grothendieck's existence theorem
for algebraic spaces (Stacks 0CXB).

The proof is the reduction
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_finitePresentationHom_existence`:
Coh is a stack in groupoids with representable diagonal (Stacks 08KC and 08W6), the base is
replaced by an étale atlas, the base scheme by `Spec ℤ` and the target by affine schemes of finite
type over `ℤ`, and Artin's criterion (Stacks 07Y4) is verified through Stacks 08KD, 08LQ, 08W8,
08W9, 07PX and the openness of versality of Stacks 0CXU. Its two inputs are the finite presentation
part of Stacks 08K6, supplied here by
`isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation` in the namespace
`AlgebraicGeometry.Space.HomSituation`, and Stacks 0CXB, which remains the hypothesis `h0CXB`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_of_existence`: Stacks 09DS
  from Stacks 0CXB, which enters as the hypothesis `h0CXB`.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

attribute [local instance] pointTopology

/-- **Stacks 09DS from Stacks 0CXB.** Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic
spaces over `S` which is of finite presentation (a field of the standing datum `D` of Situation
08KB) and separated. Then `Coh_{X/Y}` is an algebraic stack over `S`, given Grothendieck's existence
theorem for algebraic spaces, Stacks 0CXB (`h0CXB`): in Situation 0CX4 there is a finitely presented
module on `X`, flat over `A`, with support proper over `A`, restricting to the `Fₙ` compatibly with
the `φₙ`.

The finite presentation part of Stacks 08K6 is
`isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation` in the namespace
`AlgebraicGeometry.Space.HomSituation`, used over `Spec ℤ`. -/
theorem isAlgebraicStack_coherentCFG_of_existence.{w} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
    (hsep : IsSeparated B S hS D.f.hom)
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
                      (α n).hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val :=
  D.isAlgebraicStack_of_finitePresentationHom_existence hsep
    (fun s' hfp' hF hG hGflat hGsupp =>
      s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF hG hGflat
        hGsupp)
    h0CXB

end AlgebraicGeometry.Space.CoherentSituation

end
