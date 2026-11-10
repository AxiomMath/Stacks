module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationSectionsGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationBaseChangeAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationConeLift

/-!
# The stalk of a direct image over the directed system of neighbourhoods

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `U` an open subscheme
containing the image of `s`, and `N : αᵒᵖ ⥤` (étale neighbourhoods of `s`) the composite of the
directed initial system of `AlgebraicGeometry.etaleNeighborhoodDirectedFunctor` with the
inclusions into all étale neighbourhoods. As `N` is initial, the stalk `(f_*F)_s` is the colimit
of the sections `F(X ×_S N_a)`; so the map
`AlgebraicGeometry.pushforwardStalkToSectionsAb : (f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`
is an isomorphism as soon as the restrictions `F(X ×_S N_a) ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`
exhibit their target as that colimit, which is degree zero of [Stacks, Tag 03Q6].

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodDirectedNeighborhoods` — the initial functor `N`.
* `AlgebraicGeometry.strictHenselizationSectionsCocone` — the cocone of restrictions.

## Main results

* `AlgebraicGeometry.isIso_pushforwardStalkToSectionsAb_of_isColimit` — the isomorphism, from the
  colimit property of that cocone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U) {X : Scheme.{u}} (f : X ⟶ S)

/-- The directed system of affine étale neighbourhoods of `s` over `U`, as étale neighbourhoods
of `s` in the small étale site of `S`. -/
abbrev etaleNeighborhoodDirectedNeighborhoods :
    (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ ⥤
      (Scheme.pointSmallEtale s.hom).fiber.Elements :=
  etaleNeighborhoodDirectedFunctor B S hS s U hU ⋙ etaleNeighborhoodOpenInclusion B S hS s U ⋙
    etaleNeighborhoodForgetCutoff B S hS s

/-- The directed system of affine étale neighbourhoods of `s` over `U` is initial among all
étale neighbourhoods of `s`. -/
instance initial_etaleNeighborhoodDirectedNeighborhoods :
    (etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).Initial := by
  have := initial_etaleNeighborhoodOpenInclusion B S hS s U hU
  infer_instance

/-- The comparison `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, defined on germs. -/
abbrev strictHenselizationSectionsMap :
    smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1} :=
  pushforwardStalkToSectionsAb B hS f s (strictHenselizationBaseChangeToSource B hS f s)
    (strictHenselizationBaseChangeToStrictHenselization B hS f s) pullback.condition

/-- **The cocone of restrictions** `F(X ×_S N_a) ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` over the
directed system of neighbourhoods. -/
abbrev strictHenselizationSectionsCocone (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    Cocone ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).op ⋙
      (Functor.Elements.π (Scheme.pointSmallEtale s.hom).fiber).op ⋙
        ((smallEtalePushforwardAb f).obj F).obj) :=
  (((Scheme.pointSmallEtale s.hom).presheafFiberCocone
      ((smallEtalePushforwardAb f).obj F).obj).whisker
    (etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).op).extend
      ((strictHenselizationSectionsMap B S hS s f).app F)

/-- The legs of the cocone are the restrictions of sections. -/
theorem strictHenselizationSectionsCocone_ι_app (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖᵒᵖ) :
    (strictHenselizationSectionsCocone B S hS s U hU f F).ι.app a =
      pushforwardSectionsStage B hS f s (strictHenselizationBaseChangeToSource B hS f s)
        (strictHenselizationBaseChangeToStrictHenselization B hS f s) pullback.condition F
        ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).obj a.unop).1
        ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).obj a.unop).2 :=
  toPresheafFiber_comp_pushforwardStalkToSectionsAb_app B hS f s _ _ _ F _ _

/-- **The comparison is an isomorphism once the restrictions exhibit
`Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` as the colimit of the `F(X ×_S N_a)`.** -/
theorem isIso_pushforwardStalkToSectionsAb_of_isColimit
    (h : ∀ F, IsColimit (strictHenselizationSectionsCocone B S hS s U hU f F)) :
    IsIso (strictHenselizationSectionsMap B S hS s f) := by
  have : ∀ F, IsIso ((strictHenselizationSectionsMap B S hS s f).app F) := fun F => by
    have hc := (Functor.Final.isColimitWhiskerEquiv
      (etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).op _).symm
        ((Scheme.pointSmallEtale s.hom).isColimitPresheafFiberCocone
          ((smallEtalePushforwardAb f).obj F).obj)
    let e := Cocone.extendHom ((((Scheme.pointSmallEtale s.hom).presheafFiberCocone
      ((smallEtalePushforwardAb f).obj F).obj).whisker
        (etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).op))
          ((strictHenselizationSectionsMap B S hS s f).app F)
    have : IsIso e := IsColimit.hom_isIso hc (h F) e
    exact (Cocone.forget _).map_isIso e
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry

end
