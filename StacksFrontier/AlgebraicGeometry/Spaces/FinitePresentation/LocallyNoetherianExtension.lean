module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsBigFppf

/-!
# Morphisms of algebraic spaces locally of finite type are determined on locally Noetherian schemes

Let `S` be a locally Noetherian scheme and let `X'` and `X` be algebraic spaces locally of finite
type over `S`. Every transformation between the functors of points of `X'` and `X` restricted to
the locally Noetherian schemes over `S` comes from exactly one morphism `X' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.limitPreserving_of_isLocallyOfFiniteType`: over a locally Noetherian
  base an algebraic space locally of finite type is limit preserving (Stacks 05N0).
* `AlgebraicGeometry.Space.existsUnique_hom_whiskerRight_whiskerLeft_eq`: the extension statement,
  for transformations between the functors of points lifted to `Type (u + 1)` as in
  `AlgebraicGeometry.morOnLocallyNoetherian`.

## References

* [Stacks Project, Tag 05N0](https://stacks.math.columbia.edu/tag/05N0)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Over a locally Noetherian base an algebraic space locally of finite type is limit
preserving. -/
theorem limitPreserving_of_isLocallyOfFiniteType [IsLocallyNoetherian S]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS (terminal.from X)) :
    LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X := by
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e (isAlgebraicSpace_yoneda B S hS _)
  have hid : ∀ (P : MorphismProperty Scheme.{u}), P.RespectsIso → P.ContainsIdentities →
      (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf e.hom := fun P hP _ =>
    presheaf_of_isIso B S hS (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => by simpa using MorphismProperty.id_mem P ((BigFppfOver.toScheme B S hS).obj U))
      e.hom
  have hN : HasEtaleLocalProperty B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    ⟨Over.mk (𝟙 (B.obj hS)), e.hom,
      hid _ MorphismProperty.IsStableUnderBaseChange.respectsIso
        MorphismProperty.IsMultiplicative.toContainsIdentities,
      hid _ MorphismProperty.IsStableUnderBaseChange.respectsIso
        MorphismProperty.IsMultiplicative.toContainsIdentities,
      (inferInstance : IsLocallyNoetherian S)⟩
  exact (isLocallyOfFinitePresentation_terminal_iff_limitPreserving B S hS hX).1
    (isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS hX hT _ hN hft)

/-- Let `S` be locally Noetherian and let `X'` and `X` be algebraic spaces locally of finite type
over `S`. Every transformation between the functors `V ↦ Mor_S(V, X')` and `V ↦ Mor_S(V, X)` on
the locally Noetherian schemes `V` over `S` (with values lifted to `Type (u + 1)`) is induced by
exactly one morphism `X' ⟶ X`. -/
theorem existsUnique_hom_whiskerRight_whiskerLeft_eq [IsLocallyNoetherian S]
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX'ft : IsLocallyOfFiniteType B S hS (terminal.from X'))
    (hX : IsAlgebraicSpace B S hS X) (hXft : IsLocallyOfFiniteType B S hS (terminal.from X))
    (σ : (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ X' ⋙
          uliftFunctor.{u + 1} ⟶
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ X ⋙
          uliftFunctor.{u + 1}) :
    ∃! f : X' ⟶ X, Functor.whiskerRight (Functor.whiskerLeft
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op f)
        uliftFunctor.{u + 1} = σ := by
  let ιN := ObjectProperty.ι (fun T : BigFppfOver B S hS =>
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))
  let hU := fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight
    (LocallyNoetherianOver B S hS)ᵒᵖ
  have hσ := hU.map_preimage (X := ιN.op ⋙ X') (Y := ιN.op ⋙ X) σ
  obtain ⟨f, hf, huniq⟩ := ExtendingFunctors.existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS
    hX'.isSheaf (limitPreserving_of_isLocallyOfFiniteType B S hS hX' hX'ft)
    hX.isSheaf (limitPreserving_of_isLocallyOfFiniteType B S hS hX hXft)
    (hU.preimage (X := ιN.op ⋙ X') (Y := ιN.op ⋙ X) σ)
  refine ⟨f, ?_, fun f' hf' => huniq f' (hU.map_injective ?_)⟩
  · exact (congrArg (fun γ => Functor.whiskerRight γ uliftFunctor.{u + 1}) hf).trans hσ
  · exact hf'.trans hσ.symm

end AlgebraicGeometry.Space

end
