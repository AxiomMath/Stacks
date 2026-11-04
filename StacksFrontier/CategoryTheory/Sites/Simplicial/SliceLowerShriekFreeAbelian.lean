module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.CohomologyPresheafResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekRestriction

/-!
# The free abelian sheaf on a restricted sheaf, extended by zero

Let `(C, J)` be a small site and `K` a semi-representable object of `C`. On sheaves of sets,
`j_! j^{-1} G` is the product `G × F(K)^♯` (Stacks 0D87 part (2),
`CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso`). This module carries
that statement across the free abelian sheaf functor, so that on abelian sheaves
`j_! j^{-1} ℤ_G^♯` is `ℤ_{G × F(K)^♯}^♯`.

## Main results

* `CategoryTheory.SemiRepresentable.freeSheafPushforwardIso`: restriction along `j` commutes with
  the free abelian sheaf functor.
* `CategoryTheory.SemiRepresentable.freeSheafPullbackIso`: extension by zero along `j` commutes
  with the free abelian sheaf functor.
* `CategoryTheory.SemiRepresentable.freeSheafPushforwardCompSheafPullbackIso`: the two combined
  with Stacks 0D87 part (2).
* `CategoryTheory.SemiRepresentable.freeYonedaSheafPushforwardPullbackIso`: the same read at the
  free abelian sheaf on a representable, `j_! j^{-1} ℤ_V^♯ ≅ ℤ_{h_V × F(K)}^♯`.

## Implementation notes

The two commutations have different proofs. For extension by zero both composites are left
adjoints of one and the same functor — restriction along `j` followed by the underlying sheaf of
sets, in either order, which is the same functor on the nose — so uniqueness of left adjoints
applies. For restriction the composites are not left adjoints, and the content is that
restriction along `j` commutes with sheafification, which is
`CategoryTheory.Functor.pushforwardContinuousSheafificationCompatibility` for the localization
functor `j`, continuous and cocontinuous by Stacks 0D85; applying the sectionwise free abelian
group commutes with restriction of presheaves strictly.

The object-level statement at a representable turns the sheaf-valued `Sheaf.composeAndSheafify`
spelling of the free abelian sheaf into the presheaf-valued one, which is
`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso`; it needs the free abelian group
functor to preserve sheafification, which it does, being a left adjoint. The product of the two
sheafifications is read as the sheafification of the product of the presheaves: the monoidal
product of the cartesian monoidal structure on sheaves of sets is a binary product, and
sheafification is left exact.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
-- Mathlib's instance that a left adjoint preserves sheafification, tried first: at its default
-- priority the search for `J.PreservesSheafification AddCommGrpCat.free` runs out of budget.
attribute [local instance high] Sheaf.instPreservesSheafificationOfIsLeftAdjoint

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : FormalCoproduct.{u} C)

/-- **Restriction along `j : C / K ⥤ C` commutes with the free abelian sheaf functor.** Applying
the sectionwise free abelian group commutes with restriction of presheaves strictly, and
restriction commutes with sheafification because `j` is continuous and cocontinuous. -/
def freeSheafPushforwardIso :
    Sheaf.composeAndSheafify J AddCommGrpCat.free ⋙
        (componentOverForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J K) J ≅
      (componentOverForget K).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J K) J ⋙
        Sheaf.composeAndSheafify (componentwiseTopology J K) AddCommGrpCat.free :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf J (Type u) ⋙
      (Functor.whiskeringRight Cᵒᵖ (Type u) AddCommGrpCat.{u}).obj AddCommGrpCat.free)
    ((componentOverForget K).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u} (componentwiseTopology J K) J).symm

/-- **Extension by zero along `j : C / K ⥤ C` commutes with the free abelian sheaf functor.**
Both composites are left adjoint to restriction along `j` followed by the underlying sheaf of
sets, and that composite does not depend on the order in which the two operations are
performed. -/
def freeSheafPullbackIso :
    Sheaf.composeAndSheafify (componentwiseTopology J K) AddCommGrpCat.free ⋙
        Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K)
          AddCommGrpCat.{u} (componentwiseTopology J K) J ≅
      Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) (Type u)
          (componentwiseTopology J K) J ⋙
        Sheaf.composeAndSheafify J AddCommGrpCat.free :=
  Adjunction.leftAdjointUniq
    ((Sheaf.adjunction (componentwiseTopology J K) AddCommGrpCat.adj).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
        AddCommGrpCat.{u} (componentwiseTopology J K) J))
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
        (Type u) (componentwiseTopology J K) J).comp
      (Sheaf.adjunction J AddCommGrpCat.adj))

section

variable [J.WEqualsLocallyBijective (Type u)]

/-- **Stacks 0D87 part (2) on free abelian sheaves.** Restricting the free abelian sheaf on a
sheaf of sets `G` to `C / K` and extending it by zero again gives the free abelian sheaf on the
product `G × F(K)^♯`. -/
def freeSheafPushforwardCompSheafPullbackIso :
    Sheaf.composeAndSheafify J AddCommGrpCat.free ⋙
        (componentOverForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
            (componentwiseTopology J K) J ⋙
          Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K)
            AddCommGrpCat.{u} (componentwiseTopology J K) J ≅
      toOver (formalCoproductSheafification J K) ⋙
        Over.forget (formalCoproductSheafification J K) ⋙
          Sheaf.composeAndSheafify J AddCommGrpCat.free :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (freeSheafPushforwardIso J K) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (freeSheafPullbackIso J K) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafPushforwardCompSheafPullbackIso J K) _ ≪≫
    Functor.associator _ _ _

/-- **The product of two sheafifications is the sheafification of the product of the
presheaves**: the monoidal product of a cartesian monoidal category is a binary product, and
sheafification is left exact. -/
def sheafificationProdIso (P Q : Cᵒᵖ ⥤ Type u) :
    MonoidalCategory.tensorObj ((presheafToSheaf J (Type u)).obj P)
        ((presheafToSheaf J (Type u)).obj Q) ≅
      (presheafToSheaf J (Type u)).obj (P ⨯ Q) :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫
    (PreservesLimitPair.iso (presheafToSheaf J (Type u)) P Q).symm

/-- The free abelian sheaf on the cartesian monoidal product of two sheafifications is the free
abelian sheaf on the product of the two presheaves. -/
def freeAbelianSheafTensorIso (P Q : Cᵒᵖ ⥤ Type u) :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj
        (MonoidalCategory.tensorObj ((presheafToSheaf J (Type u)).obj P)
          ((presheafToSheaf J (Type u)).obj Q)) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj ((P ⨯ Q) ⋙ AddCommGrpCat.free) :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).mapIso (sheafificationProdIso J P Q) ≪≫
    (presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app (P ⨯ Q)

/-- **`j_! j^{-1} ℤ_V^♯ = ℤ_{h_V × F(K)}^♯`.** Restricting the free abelian sheaf on a
representable `h_V` to `C / K` and extending it by zero again gives the free abelian sheaf on the
presheaf `h_V × F(K)`.

This is `freeSheafPushforwardCompSheafPullbackIso` read at the sheafification of `h_V`, together
with the identification of the free abelian sheaf functor on presheaves with sheafification
followed by `Sheaf.composeAndSheafify`
(`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso`, available because the free abelian
group functor is a left adjoint and so preserves sheafification). -/
def freeYonedaSheafPushforwardPullbackIso (V : C) :
    (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) AddCommGrpCat.{u}
          (componentwiseTopology J K) J).obj
        (((componentOverForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J K) J).obj
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≅
      (presheafToSheaf J AddCommGrpCat.{u}).obj
        ((yoneda.obj V ⨯ (FormalCoproduct.yoneda (C := C)).obj K) ⋙ AddCommGrpCat.free) :=
  ((componentOverForget K).sheafPushforwardContinuous AddCommGrpCat.{u}
          (componentwiseTopology J K) J ⋙
        Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K)
          AddCommGrpCat.{u} (componentwiseTopology J K) J).mapIso
      ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app
        (yoneda.obj V)).symm ≪≫
    (freeSheafPushforwardCompSheafPullbackIso J K).app
      ((presheafToSheaf J (Type u)).obj (yoneda.obj V)) ≪≫
    freeAbelianSheafTensorIso J (yoneda.obj V) ((FormalCoproduct.yoneda (C := C)).obj K)

end

end CategoryTheory.SemiRepresentable

end
