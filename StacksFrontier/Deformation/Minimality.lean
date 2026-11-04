module

public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.TangentSpace.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Normalized and minimal groupoids in functors

Normalized and minimal groupoids in functors.

## Main definitions

* `Deformation.GroupoidInFunctors.IsNormalized` is **part (1)** of Tag 06KM: the groupoid
  `(U(k[ε]), R(k[ε]), s, t, c)` obtained by evaluating at the dual numbers is totally
  disconnected, i.e. there are no arrows between distinct objects.
* `Deformation.GroupoidInFunctors.IsMinimal` is **part (2)** of Tag 06KM: the quotient
  morphism `U → [U/R]` is given by a minimal versal formal object of `[U/R]`.

## Implementation notes

The dual numbers are the canonical Artinian square-zero extension. In part (2), "`U → [U/R]`
is given by `ξ`" is formulated as the existence of a vertical natural isomorphism between the
quotient morphism and the morphism associated to `ξ`, transported along an equivalence over
`𝒞_Λ` that prorepresents `U` by `ξ.base`. This avoids demanding an equality of presentations,
which would not be stable under the choice of pushforwards that `ξ ↦ ξ^#` depends on.

## References

* [Stacks Project, Tag 06KM](https://stacks.math.columbia.edu/tag/06KM)
-/

@[expose] public section

namespace Deformation

/-! ### Normalized and minimal groupoids in functors -/

section
open CategoryTheory
universe u v w z


namespace GroupoidInFunctors

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06KM, part (1).** A smooth prorepresentable groupoid in functors
`(U, R, s, t, c)` is *normalized* when the groupoid `(U(k[ε]), R(k[ε]), s, t, c)` obtained by
evaluating at the dual numbers `k[ε]` is totally disconnected: there are no arrows between
distinct objects.

Total disconnection is stated here in the equivalent pointwise form: every element of
`R(k[ε])`, i.e. every arrow of the evaluated groupoid, has equal source and target. -/
@[stacks 06KM "normalized",
  sga "7 VI 2.11" "normalized"]
public abbrev IsNormalized (G : GroupoidInFunctors
  (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) : Prop := ∀ a : G.arrows.obj (artinianDualNumbers Λ k),
    G.source.app (artinianDualNumbers Λ k) a = G.target.app (artinianDualNumbers Λ k) a

/-- **Stacks Project, Tag 06KM, part (2).** A smooth prorepresentable groupoid in functors
`(U, R, s, t, c)` is *minimal* when the quotient morphism `U → [U/R]` is given by a minimal
versal formal object of `[U/R]`.

Here `p : [U/R] ⥤ 𝒞_Λ` is the structure morphism of the quotient category, realized as
`Grothendieck.forget (evaluationFunctor G)`, and the data asserted to exist are:

* `ξ`, a formal object of `[U/R]`, required by the first conjunct to be minimal versal
  (`IsMinimalVersal`, Tag 06T4): this is the source's "minimal versal formal object
  of `[U/R]`";
* `pushforwards`, a choice of cocartesian pushforwards in `[U/R]`. This is the auxiliary
  data needed to build the morphism `ξ^#` associated to `ξ` (`associatedMorphism`, Tag
  06HC), which goes from the category of elements of `restrictedCoyoneda ξ.base` to
  `[U/R]`; "the morphism given by `ξ`" means `ξ^#`;
* `e`, an equivalence from the category of elements of the object functor `U` to that of
  `restrictedCoyoneda ξ.base`. The second conjunct, `e.functor ⋙ π = π`, says that `e`
  commutes with the projections to `𝒞_Λ`, i.e. that it is an equivalence *over* `𝒞_Λ`;
  it is this that lets `ξ^#` be read as a morphism `e.functor ⋙ ξ^#` out of `U`;
* the third conjunct: a natural isomorphism `α` from `quotientMorphism G`, which is the
  quotient morphism `U → [U/R]`, to `e.functor ⋙ ξ^#`, every component of which lies over
  an identity arrow of `𝒞_Λ` (`Functor.IsHomLift p (𝟙 X.1)`). Being isomorphic by such a
  vertical natural isomorphism is the sense in which `U → [U/R]` *is* given by `ξ`. -/
@[stacks 06KM "minimal"]
public def IsMinimal
    (G : GroupoidInFunctors.{_, max v w, max (max v w) z}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k)) : Prop :=
  let p := Grothendieck.forget (evaluationFunctor G)
  ∃ (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (e : G.objects.Elements ≌ (restrictedCoyoneda ξ.base).Elements),
    IsMinimalVersal (quotientProjection_cofibered G) ξ ∧
    (e.functor ⋙ CategoryOfElements.π (restrictedCoyoneda ξ.base) =
      CategoryOfElements.π G.objects) ∧
    Nonempty
      { α : quotientMorphism G ≅
          e.functor ⋙ (associatedMorphism (quotientProjection_cofibered G) ξ
            pushforwards).toBasedFunctor.toFunctor //
        ∀ X : G.objects.Elements,
          CategoryTheory.Functor.IsHomLift p (𝟙 X.1) (α.hom.app X) }

/-- **Stacks Project, Tag 06KM, part (2).** A minimal groupoid in functors has a minimal versal
formal object of its quotient: the object `ξ` whose associated morphism the quotient morphism
`U → [U/R]` is given by. This states the first conjunct of `IsMinimal` on its own, so that the
content of part (2) is available as a theorem and not only inside the definition. -/
@[stacks 06KM "minimal: the quotient has a minimal versal formal object"]
public theorem exists_isMinimalVersal_of_isMinimal
    {G : GroupoidInFunctors.{_, max v w, max (max v w) z}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (hG : IsMinimal.{u, v, w, z} G) :
    ∃ ξ : FormalObject (Grothendieck.forget (evaluationFunctor G)),
      IsMinimalVersal (quotientProjection_cofibered G) ξ := by
  obtain ⟨ξ, _, _, hmin, _, _⟩ := hG
  exact ⟨ξ, hmin⟩

/-- **Stacks Project, Tag 06KM, part (2).** For a minimal groupoid in functors, the quotient
morphism `U → [U/R]` is, up to a vertical natural isomorphism and the equivalence
prorepresenting `U`, the morphism associated to a minimal versal formal object of `[U/R]`. This
is part (2) in full, stated as a theorem. -/
@[stacks 06KM "minimal: the quotient morphism is the one associated to that object"]
public theorem exists_quotientMorphism_iso_associatedMorphism_of_isMinimal
    {G : GroupoidInFunctors.{_, max v w, max (max v w) z}
      (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (hG : IsMinimal.{u, v, w, z} G) :
    ∃ (ξ : FormalObject (Grothendieck.forget (evaluationFunctor G)))
      (pushforwards : ChosenPushforwards (Grothendieck.forget (evaluationFunctor G)))
      (e : G.objects.Elements ≌ (restrictedCoyoneda ξ.base).Elements),
      IsMinimalVersal (quotientProjection_cofibered G) ξ ∧
      (e.functor ⋙ CategoryOfElements.π (restrictedCoyoneda ξ.base) =
        CategoryOfElements.π G.objects) ∧
      Nonempty
        { α : quotientMorphism G ≅
            e.functor ⋙ (associatedMorphism (quotientProjection_cofibered G) ξ
              pushforwards).toBasedFunctor.toFunctor //
          ∀ X : G.objects.Elements,
            CategoryTheory.Functor.IsHomLift
              (Grothendieck.forget (evaluationFunctor G)) (𝟙 X.1) (α.hom.app X) } :=
  hG

end GroupoidInFunctors

end

end Deformation
