module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# A colimit of sheaves is the sheafification of the colimit of the underlying presheaves

Let `(C, J)` be a site in which sheafification of `C`-presheaves with values in `A` exists and
let `F : K ⥤ Sheaf J A` be a diagram of sheaves whose underlying diagram of presheaves has a
colimit. The colimit of the presheaves receives the colimit cocone of the sheaves, and so there
is a canonical comparison morphism of presheaves

`colim_k (F k) ⟶ (colim_k F k)_presheaf`.

This file proves that this comparison is a sheafification: it lies in
`CategoryTheory.GrothendieckTopology.W`, the class of morphisms of presheaves which become
isomorphisms after sheafification, and hence is locally bijective whenever `J.W` is the class of
locally bijective morphisms. In other words a colimit of sheaves *is* the sheafification of the
colimit of the underlying presheaves, in the form in which a functor defined on presheaves and
inverting `J.W` can consume it.

## Main definitions

* `CategoryTheory.Sheaf.colimitToColimitObj`: the comparison morphism of presheaves.

## Main results

* `CategoryTheory.Sheaf.w_colimitToColimitObj`: the comparison lies in `J.W`.
* `CategoryTheory.Sheaf.isLocallyInjective_colimitToColimitObj` and
  `CategoryTheory.Sheaf.isLocallySurjective_colimitToColimitObj`: hence it is locally bijective.

## Implementation notes

`CategoryTheory.Sheaf.sheafifyCocone` already exhibits one colimit cocone of `F` whose summit is
the sheafification of the colimit of the underlying presheaves, so the statement could be read
off from it. The proof here does not go through that cocone: it is shorter to observe that
sheafification carries both cocones in sight to colimit cocones — the first because
`CategoryTheory.presheafToSheaf` is a left adjoint, the second because
`CategoryTheory.sheafToPresheaf ⋙ CategoryTheory.presheafToSheaf` is isomorphic to the identity,
the counit of a reflective adjunction being invertible — and that the comparison is the induced
morphism between them, which is therefore invertible. That is exactly the characterisation
`CategoryTheory.GrothendieckTopology.W_iff` of `J.W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w' v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {A : Type*} [Category* A]
  [HasWeakSheafify J A] {K : Type*} [Category* K] (F : K ⥤ Sheaf J A)
  [HasColimit (F ⋙ sheafToPresheaf J A)] [HasColimit F]

/-- **The comparison of the colimit of the underlying presheaves of a diagram of sheaves with
the underlying presheaf of the colimit**: the morphism out of the colimit of presheaves induced
by the colimit cocone of sheaves, read on underlying presheaves. -/
noncomputable def colimitToColimitObj :
    colimit (F ⋙ sheafToPresheaf J A) ⟶ (colimit F).obj :=
  colimit.desc _ ((sheafToPresheaf J A).mapCocone (colimit.cocone F))

omit [HasWeakSheafify J A] in
/-- The composite of the `k`-th coprojection into the colimit of the underlying presheaves with
the comparison morphism is the underlying morphism of presheaves of the `k`-th coprojection into
the colimit of sheaves. -/
@[reassoc (attr := simp)]
lemma ι_colimitToColimitObj (k : K) :
    colimit.ι (F ⋙ sheafToPresheaf J A) k ≫ colimitToColimitObj J F =
      (colimit.ι F k).hom :=
  colimit.ι_desc _ k

/-- **A colimit of sheaves is the sheafification of the colimit of the underlying
presheaves**: the comparison morphism becomes an isomorphism after sheafification. -/
theorem w_colimitToColimitObj : J.W (colimitToColimitObj J F) := by
  rw [J.W_iff]
  have hpres : PreservesColimit F (sheafToPresheaf J A ⋙ presheafToSheaf J A) :=
    preservesColimit_of_natIso _ (asIso (sheafificationAdjunction J A).counit).symm
  have h₁ : IsColimit ((presheafToSheaf J A).mapCocone
      (colimit.cocone (F ⋙ sheafToPresheaf J A))) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  have h₂ : IsColimit ((presheafToSheaf J A).mapCocone
      ((sheafToPresheaf J A).mapCocone (colimit.cocone F))) :=
    isColimitOfPreserves (sheafToPresheaf J A ⋙ presheafToSheaf J A) (colimit.isColimit _)
  have key : (presheafToSheaf J A).map (colimitToColimitObj J F) =
      (IsColimit.coconePointUniqueUpToIso h₁ h₂).hom := by
    refine h₁.hom_ext fun k => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    dsimp only [Functor.mapCocone, Cocone.functoriality]
    rw [← Functor.map_comp]
    exact congrArg _ (ι_colimitToColimitObj J F k)
  rw [key]
  infer_instance

variable {FA : A → A → Type*} {CA : A → Type w'} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory.{w'} A FA] [J.WEqualsLocallyBijective A]

/-- If `J.W` is the class of locally bijective morphisms, the comparison morphism is locally
injective. -/
instance isLocallyInjective_colimitToColimitObj :
    Presheaf.IsLocallyInjective J (colimitToColimitObj J F) :=
  (w_colimitToColimitObj J F).isLocallyInjective

/-- If `J.W` is the class of locally bijective morphisms, the comparison morphism is locally
surjective. -/
instance isLocallySurjective_colimitToColimitObj :
    Presheaf.IsLocallySurjective J (colimitToColimitObj J F) :=
  (w_colimitToColimitObj J F).isLocallySurjective

end CategoryTheory.Sheaf

end
