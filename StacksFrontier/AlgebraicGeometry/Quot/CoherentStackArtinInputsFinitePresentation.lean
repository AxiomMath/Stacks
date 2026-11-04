module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinInputs
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTangentSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizerFinitePresentation

/-!
# Stacks 09DS from the finite presentation part of Stacks 08K6 and from Stacks 0CXB

For a separated morphism `f : X ⟶ Y` of finite presentation of algebraic spaces over any base
scheme, `Coh_{X/Y}` is an algebraic stack, given the finite presentation part of Stacks 08K6 over
`Spec ℤ` and Grothendieck's existence theorem for algebraic spaces, Stacks 0CXB.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_finitePresentationHom_existence`:
  Stacks 09DS at the source's hypotheses, from the finite presentation part of Stacks 08K6 and
  from Stacks 0CXB. The diagonal is Stacks 08W6, in the same namespace
  (`coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom`), and the tangent spaces are
  Stacks 08W8 (`AlgebraicGeometry.Space.CoherentSituation.hasFiniteDimensionalTangentSpaces`).

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08W8](https://stacks.math.columbia.edu/tag/08W8)
* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

attribute [local instance] pointTopology

/-- **Stacks 09DS from Stacks 08K6 and 0CXB.** For a separated morphism `f : X ⟶ Y` of finite
presentation of algebraic spaces over any base scheme, `Coh_{X/Y}` is an algebraic stack, given
the finite presentation part of Stacks 08K6 over `Spec ℤ` (`h08K6`) and Grothendieck's existence
theorem for algebraic spaces, Stacks 0CXB (`h0CXB`).

The diagonal over `Spec ℤ` is Stacks 08W6
(`coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom`, which uses `h08K6` through
Stacks 08K9). The tangent spaces over a scheme `V₀` locally of finite
presentation over `Spec ℤ` are Stacks 08W8
(`AlgebraicGeometry.Space.CoherentSituation.hasFiniteDimensionalTangentSpaces`): `Spec ℤ` is
locally Noetherian, and `Y = V₀` is locally of finite presentation over it
(`AlgebraicGeometry.Space.CoherentSituation.isLocallyOfFinitePresentation_terminal_from_yoneda`). -/
theorem isAlgebraicStack_of_finitePresentationHom_existence.{w} {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
    (hsep : IsSeparated B S hS D.f.hom)
    (h08K6 : ∀ (s' : HomSituation B (⊤_ Scheme.{u}) B.contains_terminal)
      (hfp' : IsFinitePresentation B _ B.contains_terminal s'.f.hom),
      s'.F.IsFinitePresentationOnSite → s'.G.IsFinitePresentationOnSite →
      IsFlatOver B _ B.contains_terminal s'.X.2 s'.f.hom s'.G →
      HasProperSupport B _ B.contains_terminal s'.X.2 s'.base.2 s'.f.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ B.contains_terminal hfp'.1)
        ((SheafOfModules.toSheaf _).obj s'.G) →
      s'.IsAffineFinitePresentationAlgebraicSpaceOverBase
        (modulePushforwardCoherence B _ B.contains_terminal))
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
  D.isAlgebraicStack_of_diagonal_tangent_existence hsep
    (fun D₀ => D₀.coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom h08K6)
    (fun V₀ hV₀ _ D₀ hY _ => by
      let eY : D₀.Y.1 ≅ yoneda.obj V₀ :=
        eqToIso (congrArg (fun Y : AlgebraicSpaces B _ B.contains_terminal => Y.1) hY)
      have h : terminal.from D₀.Y.1 = eY.hom ≫ terminal.from (yoneda.obj V₀) :=
        terminal.hom_ext _ _
      refine D₀.hasFiniteDimensionalTangentSpaces ?_
      rw [h]
      exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B _ B.contains_terminal _ eY.hom _).2
        (isLocallyOfFinitePresentation_terminal_from_yoneda B _ _ V₀ hV₀))
    h0CXB

end AlgebraicGeometry.Space.CoherentSituation

end
