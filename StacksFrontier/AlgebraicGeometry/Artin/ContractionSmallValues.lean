module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# The values of Artin's contraction functor are small

In the situation of Stacks 0GH8, Artin's functor `F` of Stacks 0GHA takes values in
`Type (u + 1)`, because its third component `x̂ : V_{/Z} ⟶ W` is a morphism of fppf sheaves of
`Type (u + 1)`. This file proves that every value `F(V)` is nevertheless `u`-small. This is what
is needed to apply Stacks 0GE7, which is about set-valued functors, to `F`.

## The argument

* The values of a sheaf `X` satisfying the set-theoretic condition of Stacks 0AIS are `u`-small
  (`AlgebraicGeometry.FormalSpace.small_obj_of_satisfiesSetTheoreticCondition`): a representable
  sheaf surjects onto `X`, so every section of `X` lies locally in the image of a `u`-small
  presheaf, and `AlgebraicGeometry.Space.small_of_sieveOfSection_mem` applies on the essentially
  small big fppf site. In particular this holds for the formal algebraic space `W`.
* Morphisms between presheaves with `u`-small values on the big fppf site form a `u`-small type
  (`AlgebraicGeometry.small_hom_of_small`), by shrinking both presheaves to `Type u` and using
  `AlgebraicGeometry.small_hom_presheaf`.
* A triple `(Z, u', x̂)` is determined by `Z`, by `u'` and by the composition of `x̂` with the
  sheafification map of the completion subfunctor, a morphism of presheaves with `u`-small values.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.small_contractionFunctor_obj`: `F(V)` is
  `u`-small for every locally Noetherian `V` over `S`.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GE7](https://stacks.math.columbia.edu/tag/0GE7)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Morphisms between presheaves of `Type (u + 1)` with `u`-small values on the big fppf site of
`S` form a `u`-small type. -/
theorem small_hom_of_small {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    [FunctorToTypes.Small.{u} P] [FunctorToTypes.Small.{u} Q] : Small.{u} (P ⟶ Q) := by
  have := small_hom_presheaf (FunctorToTypes.shrink.{u} P) (FunctorToTypes.shrink.{u} Q)
  refine small_of_injective (f := fun τ => FunctorToTypes.shrinkMap.{u} τ) fun τ τ' h => ?_
  ext X x
  simpa using congrArg (fun σ => σ.app X (equivShrink _ x)) h

namespace FormalSpace

/-- **The sections of a sheaf satisfying the set-theoretic condition of Stacks 0AIS are
`u`-small.** -/
theorem small_obj_of_satisfiesSetTheoreticCondition {X : FppfSheaf B S hS}
    (hX : SatisfiesSetTheoreticCondition B S hS X) (T : BigFppfOver B S hS) :
    Small.{u} (X.obj.obj (op T)) := by
  obtain ⟨U, -, hU, -, ⟨eU⟩, -, f, hf, -⟩ := hX
  have _ := Stack.essentiallySmall_bigFppfOver B S hS
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f.hom :=
    (Sheaf.isLocallySurjective_iff_epi f).2 hf
  refine Space.small_of_sieveOfSection_mem X.property (Subfunctor.range f.hom) (fun Y x => ?_)
    (fun Y => ?_) T
  · exact Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f.hom x
  · have : Small.{u} ((uliftYoneda.{u + 1}.obj U).obj (op Y)) :=
      inferInstanceAs (Small.{u} (ULift.{u + 1} (Y ⟶ U)))
    have : Small.{u} (hU.obj.obj (op Y)) :=
      small_map (eU.app (op Y)).toEquiv
    exact small_range _

end FormalSpace

namespace Artin.ContractionSituation

variable (c : ContractionSituation B S hS)

/-- **The values of Artin's contraction functor are `u`-small**: for every object `V` of the big
fppf site of `S`, the triples `(Z, u', x̂)` over `V` form a `u`-small type. -/
theorem small_triple (V : BigFppfOver B S hS) : Small.{u} (Triple c V) := by
  classical
  have hW : ∀ T : (BigFppfOver B S hS)ᵒᵖ, Small.{u} (c.W.obj.obj T) := fun T =>
    FormalSpace.small_obj_of_satisfiesSetTheoreticCondition c.isLocallyNoetherian_W.1.1 T.unop
  have : FunctorToTypes.Small.{u} c.W.obj := hW
  have : Small.{u} (Set (Space.points B S hS (yoneda.obj V))) :=
    have : Small.{u} (Space.points B S hS (yoneda.obj V)) :=
      small_map (Space.pointsEquivScheme B S hS V)
    inferInstance
  have hP : ∀ Z : Set (Space.points B S hS (yoneda.obj V)),
      FunctorToTypes.Small.{u} (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor :=
    fun Z T =>
      have : Small.{u} (((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Z).toFunctor ⋙
          uliftFunctor.{u + 1}).obj T) :=
        inferInstanceAs (Small.{u} (ULift.{u + 1}
          ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Z).toFunctor.obj T)))
      small_map ((Space.completionSubfunctorIso B S hS (yoneda.obj V) Z).app T).toEquiv
  have : ∀ Z : Set (Space.points B S hS (yoneda.obj V)),
      Small.{u} ((Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ c.W.obj) :=
    fun Z => have := hP Z; small_hom_of_small
  have : ∀ Z : Set (Space.points B S hS (yoneda.obj V)),
      Small.{u} ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶
        c.U'.toFunctor) := fun Z => small_hom_presheaf _ _
  let ψ : Triple c V → Σ Z : Set (Space.points B S hS (yoneda.obj V)),
      ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor) ×
        ((Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ c.W.obj) := fun t =>
    ⟨t.Z, t.u, (BigFppfOver.topology B S hS).toSheafify _ ≫ t.xhat.hom⟩
  refine small_of_injective (f := ψ) fun t t' h => ?_
  obtain ⟨Z, hZ, u, x, a, w⟩ := t
  obtain ⟨Z', hZ', u', x', a', w'⟩ := t'
  obtain ⟨rfl, h₂⟩ := Sigma.mk.inj_iff.mp h
  obtain ⟨rfl, h₃⟩ := Prod.ext_iff.mp (eq_of_heq h₂)
  obtain rfl : x = x' :=
    Sheaf.hom_ext (GrothendieckTopology.sheafify_hom_ext _ _ _ c.W.property h₃)
  rfl

/-- **The values of Artin's contraction functor are `u`-small**, as a property of the functor on
the locally Noetherian site. -/
theorem small_contractionFunctor_obj (V : (LocallyNoetherianOver B S hS)ᵒᵖ) :
    Small.{u} ((contractionFunctor c).obj V) :=
  small_triple c V.unop.obj

end Artin.ContractionSituation

end AlgebraicGeometry
