module

public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The inverse image of sheaves of sets commutes with raising the universe

Let `G : C ⥤ D` be a continuous functor of sites. Its inverse image on sheaves of sets,
`CategoryTheory.Functor.sheafPullback`, is formed separately in each universe of sets. This file
shows that raising the universe of a sheaf of sets with `uliftFunctor` commutes with it:

`G^s(F) ⋙ ULift ≅ G^s(F ⋙ ULift)`,

as soon as the inverse image is computed in both universes by a left Kan extension followed by
sheafification and lifting the universe preserves sheafification on `D`.

## Main definitions

* `CategoryTheory.Functor.sheafComposeULiftIso`: on sheaves, composing with `uliftFunctor` is the
  sheafification of composing with `uliftFunctor`.
* `CategoryTheory.Functor.presheafToSheafULiftIso`: lifting the universe commutes with
  sheafification.
* `CategoryTheory.Functor.sheafPullbackULiftIso`: lifting the universe commutes with the
  inverse image along a continuous functor.

## Main results

* `CategoryTheory.Presheaf.isLocallyInjective_whiskerRight_uliftFunctorTypes` and
  `CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_uliftFunctorTypes`: lifting the
  universe preserves local injectivity and local surjectivity.
* `GrothendieckTopology.preservesSheafification_uliftFunctor_of_wEqualsLocallyBijective`:
  when the local isomorphisms are the locally bijective maps in both universes, lifting the
  universe preserves sheafification.

## Implementation notes

The comparison is assembled from three canonical isomorphisms: Mathlib's identification of
`CategoryTheory.Functor.sheafPullback` with the left Kan extension followed by sheafification
(`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullbackIso`), the commutation of left
Kan extensions with the colimit-preserving `uliftFunctor`
(`CategoryTheory.Functor.lanCompIsoOfPreserves`), and the commutation of sheafification with a
functor preserving sheafification
(`CategoryTheory.presheafToSheafCompComposeAndSheafifyIso`). The left Kan extension in the
smaller universe is asked to be pointwise, which is what lets `uliftFunctor` preserve it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)

/-- Lifting the universe of a locally injective morphism of presheaves of sets keeps it locally
injective: the equalizer sieve of two lifted sections is that of the sections themselves. -/
lemma isLocallyInjective_whiskerRight_uliftFunctorTypes [IsLocallyInjective J f] :
    IsLocallyInjective J (Functor.whiskerRight f uliftFunctor.{w'}) where
  equalizerSieve_mem {X} x y h := by
    have h' : f.app X x.down = f.app X y.down := congrArg ULift.down h
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J f x.down y.down h')
    intro Z g hg
    exact congrArg ULift.up hg

/-- Lifting the universe of a locally surjective morphism of presheaves of sets keeps it locally
surjective: the image sieve of a lifted section is that of the section itself. -/
lemma isLocallySurjective_whiskerRight_uliftFunctorTypes [IsLocallySurjective J f] :
    IsLocallySurjective J (Functor.whiskerRight f uliftFunctor.{w'}) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
    rintro Z g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

end Presheaf

namespace GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- When the local isomorphisms of presheaves of sets are the locally bijective morphisms in
both universes, lifting the universe preserves sheafification. -/
lemma preservesSheafification_uliftFunctor_of_wEqualsLocallyBijective
    [J.WEqualsLocallyBijective (Type w)] [J.WEqualsLocallyBijective (Type (max w w'))] :
    J.PreservesSheafification uliftFunctor.{w', w} where
  le P Q f hf := by
    rw [J.W_iff_isLocallyBijective] at hf
    obtain ⟨_, _⟩ := hf
    have := Presheaf.isLocallyInjective_whiskerRight_uliftFunctorTypes.{w, w'} J f
    have := Presheaf.isLocallySurjective_whiskerRight_uliftFunctorTypes.{w, w'} J f
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f uliftFunctor.{w'})

end GrothendieckTopology

namespace Functor

section Products

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose uliftFunctor.{w', w}]

/-- Lifting the universe of sheaves of sets preserves finite products: limits of sheaves are
computed on the underlying presheaves, and `uliftFunctor` preserves limits. -/
instance preservesFiniteProducts_sheafCompose_uliftFunctor :
    PreservesFiniteProducts (sheafCompose J uliftFunctor.{w', w}) where
  preserves n := by
    have : PreservesLimitsOfShape (Discrete (Fin n))
        (sheafCompose J uliftFunctor.{w', w} ⋙ sheafToPresheaf J (Type (max w w'))) :=
      preservesLimitsOfShape_of_natIso
        (F := sheafToPresheaf J (Type w) ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor)
        (NatIso.ofComponents (fun _ => Iso.refl _))
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J (Type (max w w')))

end Products

section Sheafification

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose uliftFunctor.{w', w}]
  [HasWeakSheafify K (Type (max w w'))]

/-- On sheaves of sets, composing with `uliftFunctor` is the sheafification of composing with
`uliftFunctor`, because the composite is already a sheaf. -/
noncomputable def sheafComposeULiftIso :
    sheafCompose K uliftFunctor.{w', w} ≅ Sheaf.composeAndSheafify K uliftFunctor.{w', w} :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (sheafCompose K uliftFunctor.{w', w})
      (asIso (sheafificationAdjunction K (Type (max w w'))).counit).symm

variable [HasWeakSheafify K (Type w)] [K.PreservesSheafification uliftFunctor.{w', w}]

/-- Lifting the universe of presheaves of sets commutes with sheafification, when it preserves
sheafification. -/
noncomputable def presheafToSheafULiftIso :
    presheafToSheaf K (Type w) ⋙ sheafCompose K uliftFunctor.{w', w} ≅
      (Functor.whiskeringRight Dᵒᵖ _ _).obj uliftFunctor.{w', w} ⋙
        presheafToSheaf K (Type (max w w')) :=
  Functor.isoWhiskerLeft (presheafToSheaf K (Type w)) (sheafComposeULiftIso.{w, w'} K) ≪≫
    presheafToSheafCompComposeAndSheafifyIso K uliftFunctor.{w', w}

end Sheafification

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [J.HasSheafCompose uliftFunctor.{w', w}] [K.HasSheafCompose uliftFunctor.{w', w}]
  [HasWeakSheafify K (Type w)] [HasWeakSheafify K (Type (max w w'))]
  [K.PreservesSheafification uliftFunctor.{w', w}]
  [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseLeftKanExtension F]
  [∀ F : Cᵒᵖ ⥤ Type (max w w'), G.op.HasLeftKanExtension F]

/-- **The inverse image of sheaves of sets commutes with raising the universe.** For a
continuous functor `G : C ⥤ D` of sites, lifting the universe of the inverse image of a sheaf of
sets is the inverse image of its lift. -/
noncomputable def sheafPullbackULiftIso :
    G.sheafPullback (Type w) J K ⋙ sheafCompose K uliftFunctor.{w', w} ≅
      sheafCompose J uliftFunctor.{w', w} ⋙ G.sheafPullback (Type (max w w')) J K :=
  Functor.isoWhiskerRight (sheafPullbackConstruction.sheafPullbackIso G (Type w) J K) _ ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type w) ⋙ G.op.lan)
      (presheafToSheafULiftIso.{w, w'} K) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type w))
      (Functor.isoWhiskerRight (uliftFunctor.{w', w}.lanCompIsoOfPreserves G.op)
        (presheafToSheaf K (Type (max w w')))) ≪≫
    Functor.isoWhiskerLeft (sheafCompose J uliftFunctor.{w', w})
      (sheafPullbackConstruction.sheafPullbackIso G (Type (max w w')) J K).symm

end Pullback

end Functor

end CategoryTheory

end
