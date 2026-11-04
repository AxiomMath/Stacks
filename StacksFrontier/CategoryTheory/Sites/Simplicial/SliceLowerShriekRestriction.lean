module

public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullNaturality
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.SheavesOverSheafification

/-!
# Lower shriek of a restricted sheaf on the site of a semi-representable object

Let `(C, J)` be a small site and `K` a semi-representable object of `C`. Stacks 0D87 identifies
sheaves on `C / K` with sheaves over `F(K)^♯` and, under that identification, restriction
`j^{-1}` with `G ↦ (G × F(K)^♯ ⟶ F(K)^♯)`. Consequently `j_! j^{-1} G` is the product
`G × F(K)^♯`.

The 0D87 statements are written in the componentwise presentation of `Sh(C / K)` as the product
`∏ i, Sh(C / K_i)`; this module transports them to the site `C / K` itself, where `j^{-1}` is
restriction along the localization functor `j : C / K ⥤ C` and `j_!` is the sheaf pullback along
it.

## Main results

* `CategoryTheory.SemiRepresentable.componentOverForget_sheafPullback_iso`: the sheaf pullback
  along `j` is the equivalence of Stacks 0D87 part (1) followed by the coproduct of the
  componentwise lower shrieks.
* `CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso`: `j_! j^{-1}` is
  `G ↦ G × F(K)^♯`.

## Implementation notes

Continuity and cocontinuity of `j`, which are Stacks 0D85, are the instances
`CategoryTheory.SemiRepresentable.componentOverForget_isContinuous` and
`.componentOverForget_isCocontinuous` of
`StacksFrontier/CategoryTheory/Sites/SemiRepresentable/PushPullNaturality.lean`.

The identification of the right adjoints is an equality rather than an isomorphism: restriction
along `j` followed by restriction to the component indexed by `i` is restriction along the
composite `C / K_i ⥤ C / K ⥤ C`, which is the localization functor `C / K_i ⥤ C` on the nose,
and both `restrictSheaf` and `GrothendieckTopology.overPullback` are precomposition of the
underlying presheaf. Uniqueness of left adjoints then transports the sheaf pullback.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : FormalCoproduct.{u} C)

variable [HasWeakSheafify J (Type u)]

omit [HasWeakSheafify J (Type u)] in
/-- Restricting a sheaf on `C` along `j : C / K ⥤ C` and then to the component slices is
restricting it to each slice: the two composite site functors `C / K_i ⥤ C` agree, and both
operations are precomposition of the underlying presheaf. -/
theorem sheafPushforwardContinuous_comp_restrictSheaf :
    (componentOverForget K).sheafPushforwardContinuous (Type u) (componentwiseTopology J K) J ⋙
        restrictSheaf J K (Type u) =
      componentwiseRestriction J K :=
  rfl

/-- The inverse of the equivalence of Stacks 0D87 part (1) turns componentwise restriction back
into restriction along `j`. -/
def componentwiseRestrictionCompInverseIso :
    componentwiseRestriction J K ⋙
        (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).inverse ≅
      (componentOverForget K).sheafPushforwardContinuous (Type u)
        (componentwiseTopology J K) J :=
  Functor.isoWhiskerRight
      (eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    (Functor.isoWhiskerLeft _
      (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unitIso).symm ≪≫
    Functor.rightUnitor _

/-- The sheaf-level lower shriek along `j : C / K ⥤ C` is the equivalence of Stacks 0D87 part (1)
followed by the coproduct of the componentwise lower shrieks: both are left adjoint to
restriction along `j`. -/
def componentOverForget_sheafPullback_iso :
    Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) (Type u)
        (componentwiseTopology J K) J ≅
      (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor ⋙
        componentShriekSigma J K :=
  Adjunction.leftAdjointUniq
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
      (Type u) (componentwiseTopology J K) J)
    (((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).toAdjunction.comp
      (componentShriekSigmaAdjunction J K)).ofNatIsoRight
        (componentwiseRestrictionCompInverseIso J K))

section

variable [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]

/-- **Stacks 0D87 part (2), read on the site `C / K`.** Restricting a sheaf `G` on `C` to
`C / K` and extending it by zero again gives the product `G × F(K)^♯`. -/
def sheafPushforwardCompSheafPullbackIso :
    (componentOverForget K).sheafPushforwardContinuous (Type u) (componentwiseTopology J K) J ⋙
        Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) (Type u)
          (componentwiseTopology J K) J ≅
      toOver (formalCoproductSheafification J K) ⋙
        Over.forget (formalCoproductSheafification J K) :=
  Functor.isoWhiskerLeft _ (componentOverForget_sheafPullback_iso J K) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)) _ ≪≫
    Functor.isoWhiskerLeft _ (componentShriekSigmaIso J K) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (componentwiseRestrictionCompSheafFunctorToOverIso J K) _

end

end CategoryTheory.SemiRepresentable

end
