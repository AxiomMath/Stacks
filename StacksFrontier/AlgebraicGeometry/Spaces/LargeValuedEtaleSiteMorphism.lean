module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Étaleness of the universe-lifted Yoneda image of a morphism of the big fppf site

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f` of presheaves on the
big fppf site of `S` with values in `Type (max w u)` is étale in the sense of
Stacks 03FR — `AlgebraicGeometry.Space.IsEtaleULift` — when composing it with any étale
morphism out of a universe-lifted Yoneda presheaf again gives a morphism that is étale after
every represented base change. For a morphism `φ` of the site itself there is a far more
concrete description available: `uliftYoneda.{w}.map φ` is étale in that sense exactly when
the morphism of schemes `(BigFppfOver.toScheme B S hS).map φ` underlying `φ` is étale.

## Main results

* `AlgebraicGeometry.Space.isEtaleULift_iff_relative_etale`: a morphism out of a
  universe-lifted Yoneda presheaf is étale in the sense of Stacks 03FR exactly when it is
  étale after every represented base change.
* `AlgebraicGeometry.Space.relative_etale_uliftYoneda_map_iff`: the universe-lifted Yoneda
  image of a morphism of the big fppf site of `S` is étale after every represented base
  change exactly when the underlying morphism of schemes is étale.
* `AlgebraicGeometry.Space.isEtaleULift_uliftYoneda_map_iff`: the universe-lifted Yoneda image
  of a morphism of the site is étale as a morphism of presheaves exactly when the underlying
  morphism of schemes is étale.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor applying `CategoryTheory.uliftFunctor` to the values of a presheaf on the big
fppf site of `S`, through which the universe-lifted Yoneda embedding factors. -/
private abbrev uliftValues :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)) :=
  (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (max w u))).obj
    uliftFunctor.{w}

/-- A relative morphism property along the universe-lifted Yoneda embedding holds for the
universe lift of a morphism of presheaves of `Type u` exactly when the relative property
along the Yoneda embedding holds for the morphism. -/
private theorem relative_uliftValues_map_iff (Q : MorphismProperty (BigFppfOver B S hS))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    Q.relative (uliftYoneda.{w}) ((uliftValues.{w} B S hS).map a) ↔ Q.presheaf a :=
  relative_comp_map_iff yoneda (uliftValues.{w} B S hS) Q a

/-! ### Étaleness after every represented base change -/

/-- A property of morphisms of the big fppf site of `S` which holds for isomorphisms holds
after every represented base change of the identity of a universe-lifted Yoneda presheaf. -/
public theorem relative_id_of_isomorphisms (Q : MorphismProperty (BigFppfOver B S hS))
    (hQ : ∀ ⦃X Y : BigFppfOver B S hS⦄ (φ : X ⟶ Y), IsIso φ → Q φ)
    (T : BigFppfOver B S hS) :
    Q.relative (uliftYoneda.{w}) (𝟙 ((uliftYoneda.{w}).obj T)) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso (uliftYoneda.{w}) _, ?_⟩
  intro A A' g fst snd hpb
  have : IsIso ((uliftYoneda.{w}).map snd) := hpb.isIso_snd_of_isIso
  exact hQ snd (Functor.FullyFaithful.isIso_of_isIso_map (ULiftYoneda.fullyFaithful _) snd)

/-- The identity of a universe-lifted Yoneda presheaf is étale after every represented base
change. -/
public theorem relative_id_etale (T : BigFppfOver B S hS) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        (𝟙 ((uliftYoneda.{w}).obj T)) := by
  refine relative_id_of_isomorphisms B S hS _ (fun _ _ φ _ => ?_) T
  show AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ)
  infer_instance

/-- Étaleness after every represented base change is stable under composition. -/
private theorem relative_etale_comp {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)}
    {m : F ⟶ G} {n : G ⟶ K}
    (hm : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) m)
    (hn : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) n) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) (m ≫ n) :=
  MorphismProperty.comp_mem _ _ _ hm hn

/-! ### The two halves of the criterion -/

/-- A morphism out of a universe-lifted Yoneda presheaf is étale in the sense of
Stacks 03FR exactly when it is étale after every represented base change. -/
theorem isEtaleULift_iff_relative_etale {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (m : (uliftYoneda.{w}).obj U ⟶ F) :
    IsEtaleULift.{w} B S hS m ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w}) m := by
  refine ⟨fun hm => ?_, fun hm _ φ hφ => relative_etale_comp B S hS hφ hm⟩
  simpa using hm U (𝟙 _) (relative_id_etale B S hS U)

/-- The universe-lifted Yoneda image of a morphism of the big fppf site of `S` is étale after
every represented base change exactly when the underlying morphism of schemes is étale. -/
theorem relative_etale_uliftYoneda_map_iff {U V : BigFppfOver B S hS} (φ : U ⟶ V) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        ((uliftYoneda.{w}).map φ) ↔
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ) :=
  (relative_uliftValues_map_iff B S hS _ (yoneda.map φ)).trans
    (presheaf_yoneda_map_etale_iff B S hS φ)

/-! ### The criterion -/

/-- **Étaleness of the universe-lifted Yoneda image of a morphism of the site.** For a
morphism `φ` of the big fppf site of `S`, the universe-lifted Yoneda image
`uliftYoneda.{w}.map φ` is étale as a morphism of presheaves with values in
`Type (max w u)`, in the sense of Stacks 03FR, exactly when the morphism of schemes
`(BigFppfOver.toScheme B S hS).map φ` underlying `φ` is étale. -/
theorem isEtaleULift_uliftYoneda_map_iff {U V : BigFppfOver B S hS} (φ : U ⟶ V) :
    IsEtaleULift.{w} B S hS ((uliftYoneda.{w}).map φ) ↔
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ) :=
  (isEtaleULift_iff_relative_etale B S hS ((uliftYoneda.{w}).map φ)).trans
    (relative_etale_uliftYoneda_map_iff B S hS φ)

end AlgebraicGeometry.Space

end
