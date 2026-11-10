module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityEventual
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityChart

/-!
# The morphism `r_ψ` of relative Projs as a morphism of algebraic spaces

Let `ψ : 𝒜 ⟶ ℬ` be a map of quasi-coherent graded algebras on an algebraic space `X`, presented
over the scheme points of `X`, with `P = Proj_X(𝒜)` and `Q = Proj_X(ℬ)`. When the scheme-level
open `U(ψ|_{T,f})` of Stacks 07ZG is everything at every scheme point `(T, f)` of `X`, the base
change of the morphism `r_ψ : U(ψ) ⟶ P` of Stacks 085F along the étale chart `T ×_X P ⟶ P` is the
scheme-level morphism `r_{ψ|_{T,f}} : Proj_T(ℬ|_T) ⟶ Proj_T(𝒜|_T)`. Hence `r_ψ` has every
base-change stable property of morphisms of schemes that all the `r_{ψ|_{T,f}}` have.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.isPullback_fibreToDomain`: the cartesian square
  identifying the base change of `r_ψ` along `T ×_X P ⟶ P` with `r_{ψ|_{T,f}}`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.presheaf_relativeMapSpaceHom`: `r_ψ` has a
  base-change stable property `W` of morphisms of schemes as soon as every `r_{ψ|_{T,f}}` has it.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.isClosedImmersion_relativeMapSpaceHom`: if every
  restriction of `ψ` is surjective in all large degrees then `r_ψ` is a closed immersion of
  algebraic spaces (Stacks 085H (2)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Filter
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πQ) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)

/-- The projection `T ×_X Q ⟶ Q` corresponds, over the structure morphism of the fibre, to the
identity section of the fibre. -/
theorem pointEquivOver_fibreToSpace :
    (d.pointEquivOver T f (d.fibreHom T f) ⟨d.fibreToSpace T f, (d.isPullback T f).w⟩).1 =
      𝟙 _ := by
  have h : (⟨d.fibreToSpace T f, (d.isPullback T f).w⟩ :
      {u : yoneda.obj (d.fibre T f) ⟶ Q // u ≫ πQ = yoneda.map (d.fibreHom T f) ≫ f}) =
      (d.pointEquivOver T f (d.fibreHom T f)).symm ⟨𝟙 _, Category.id_comp _⟩ := by
    apply Subtype.ext
    change _ = yoneda.map (𝟙 _) ≫ _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h, Equiv.apply_symm_apply]

end RelativeProjPoints

namespace RelativeProjHomPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    (hψ : RelativeProjHomPoints dP dQ)
    (hdom : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      (hψ.hom T f).relativeMapDomain = ⊤)

include hdom

/-- If the scheme-level open `U(ψ|_{T,f})` is everything at every scheme point of the base, then
`U(ψ) = Q`. -/
theorem relativeMapSubfunctor_eq_top_of_relativeMapDomain_eq_top :
    hψ.relativeMapSubfunctor = ⊤ :=
  top_le_iff.1 fun Y y _ => by
    change _ ⁻¹ᵁ _ = ⊤
    rw [hdom, Scheme.Hom.preimage_top]

/-- The projection `T ×_X Q ⟶ Q` lies in the domain of definition. -/
theorem isDefinedOn_fibreToSpace (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    IsDefinedOn dP dQ hψ.hom T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
      (dQ.isPullback T f).w := by
  change _ ⁻¹ᵁ _ = ⊤
  rw [hdom T f, Scheme.Hom.preimage_top]

/-- The projection `T ×_X Q ⟶ Q`, as a point of `U(ψ)`. -/
def fibreToDomain (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    yoneda.obj (dQ.fibre T f) ⟶ hψ.relativeMapSubfunctor.toFunctor :=
  Subfunctor.lift (dQ.fibreToSpace T f) (by
    rw [hψ.relativeMapSubfunctor_eq_top_of_relativeMapDomain_eq_top hdom]
    exact le_top)

/-- The point `fibreToDomain` of `U(ψ)` composed with the inclusion `U(ψ) ⟶ Q` is the
projection `T ×_X Q ⟶ Q`. -/
@[reassoc (attr := simp)]
theorem fibreToDomain_ι (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.fibreToDomain hdom T f ≫ hψ.relativeMapSubfunctor.ι = dQ.fibreToSpace T f :=
  rfl

/-- The point of `P` that `r_ψ` attaches to the projection `T ×_X Q ⟶ Q`. -/
abbrev fibrePoint (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    yoneda.obj (dQ.fibre T f) ⟶ P :=
  pointHomOn dP dQ hψ.hom T f (dQ.fibreHom T f) (dQ.fibreToSpace T f) (dQ.isPullback T f).w
    (hψ.isDefinedOn_fibreToSpace hdom T f)

/-- `r_ψ` sends the point `fibreToDomain` of `U(ψ)` to `fibrePoint`. -/
theorem fibreToDomain_comp_relativeMapSpaceHom (T : BigFppfOver B S hS)
    (f : yoneda.obj T ⟶ X) :
    hψ.fibreToDomain hdom T f ≫ hψ.relativeMapSpaceHom = hψ.fibrePoint hdom T f :=
  yonedaEquiv.injective <| (yonedaEquiv_comp _ _).trans <| hψ.app_relativeMapSpaceHom T f
    (dQ.fibreHom T f) (dQ.fibreToSpace T f) (dQ.isPullback T f).w
    (hψ.isDefinedOn_fibreToSpace hdom T f) _

/-- **The morphism `r_{ψ|_{T,f}}` as a morphism of the site**: the morphism of fibres
`T ×_X Q ⟶ T ×_X P` over `T` induced by `r_ψ`. -/
def fibreMap (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) : dQ.fibre T f ⟶ dP.fibre T f :=
  (dP.pointEquivOver T f (dQ.fibreHom T f)
    ⟨hψ.fibrePoint hdom T f, pointHomOn_comp dP dQ hψ.hom T f _ _ _ _⟩).1

/-- `fibreMap` is a morphism over `T`. -/
@[reassoc (attr := simp)]
theorem fibreMap_fibreHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.fibreMap hdom T f ≫ dP.fibreHom T f = dQ.fibreHom T f :=
  (dP.pointEquivOver T f (dQ.fibreHom T f)
    ⟨hψ.fibrePoint hdom T f, pointHomOn_comp dP dQ hψ.hom T f _ _ _ _⟩).2

/-- `fibreMap` followed by the projection `T ×_X P ⟶ P` is `fibrePoint`. -/
theorem yoneda_map_fibreMap_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    yoneda.map (hψ.fibreMap hdom T f) ≫ dP.fibreToSpace T f = hψ.fibrePoint hdom T f :=
  dP.map_pointEquivOver T f (dQ.fibreHom T f) ⟨_, _⟩

/-- The scheme morphism underlying `fibreMap` is `r_{ψ|_{T,f}}`, conjugated by the
identifications of the fibres with the scheme-level relative Projs. -/
theorem toScheme_map_fibreMap (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (BigFppfOver.toScheme B S hS).map (hψ.fibreMap hdom T f) =
      liftToOpens (dQ.fibreIso T f).hom (hψ.hom T f).relativeMapDomain
          (by rw [hdom T f, Scheme.Hom.preimage_top]) ≫
        relativeMapHom (hψ.hom T f) ≫ (dP.fibreIso T f).inv := by
  rw [← cancel_mono (dP.fibreIso T f).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  have h1 := dP.pointEquivProjOver_apply T f (dQ.fibreHom T f)
    ⟨hψ.fibrePoint hdom T f, pointHomOn_comp dP dQ hψ.hom T f _ _ _ _⟩
  have h2 := sectionOfPoint_pointHomOn dP dQ hψ.hom T f (dQ.fibreHom T f) (dQ.fibreToSpace T f)
    (dQ.isPullback T f).w (hψ.isDefinedOn_fibreToSpace hdom T f)
  change (dP.pointEquivProjOver T f (dQ.fibreHom T f) ⟨_, _⟩).1 = _ at h2
  rw [fibreMap, ← h1, h2]
  congr 1
  exact liftToOpens_congr _ _ (dQ.sectionOfPoint_fibreToSpace T f) _ _ _

/-- **The base change of `r_ψ` along the chart `T ×_X P ⟶ P` is `r_{ψ|_{T,f}}`.** -/
theorem isPullback_fibreToDomain (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    IsPullback (hψ.fibreToDomain hdom T f) (yoneda.map (hψ.fibreMap hdom T f))
      hψ.relativeMapSpaceHom (dP.fibreToSpace T f) := by
  have hι : IsIso hψ.relativeMapSubfunctor.ι := by
    rw [hψ.relativeMapSubfunctor_eq_top_of_relativeMapDomain_eq_top hdom]
    infer_instance
  have outer : IsPullback (hψ.fibreToDomain hdom T f) (yoneda.map (dQ.fibreHom T f))
      (hψ.relativeMapSpaceHom ≫ πP) f :=
    (dQ.isPullback T f).of_iso (Iso.refl _) (asIso hψ.relativeMapSubfunctor.ι).symm
      (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, IsIso.comp_inv_eq,
        fibreToDomain_ι])
      (by simp)
      (by rw [hψ.relativeMapSpaceHom_comp]; simp)
      (by simp)
  refine IsPullback.of_bot ?_ ?_ (dP.isPullback T f)
  · rw [← CategoryTheory.Functor.map_comp, fibreMap_fibreHom]
    exact outer
  · rw [fibreToDomain_comp_relativeMapSpaceHom, yoneda_map_fibreMap_comp]

/-- **`r_ψ` inherits base-change stable properties from the scheme-level `r_{ψ|_{T,f}}`.** If the
open `U(ψ|_{T,f})` of Stacks 07ZG is everything and the morphism `r_{ψ|_{T,f}}` has a property `W`
of morphisms of schemes, stable under base change and isomorphisms, at every scheme point
`(T, f)` of the base, then `r_ψ : U(ψ) ⟶ P` has `W` as a morphism of presheaves on the site. -/
theorem presheaf_relativeMapSpaceHom (W : MorphismProperty Scheme.{u})
    [W.IsStableUnderBaseChange] [W.RespectsIso]
    (hW : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X), W (relativeMapHom (hψ.hom T f))) :
    (W.inverseImage (BigFppfOver.toScheme B S hS)).presheaf hψ.relativeMapSpaceHom := by
  have hbc := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS W
  have hρ : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      W ((BigFppfOver.toScheme B S hS).map (hψ.fibreMap hdom T f)) := by
    intro T f
    rw [hψ.toScheme_map_fibreMap hdom T f]
    have hι : IsIso (hψ.hom T f).relativeMapDomain.ι := by
      rw [hdom T f]
      exact (Scheme.topIso _).isIso_hom
    have hl : IsIso (liftToOpens (dQ.fibreIso T f).hom (hψ.hom T f).relativeMapDomain
        (by rw [hdom T f, Scheme.Hom.preimage_top])) := by
      have e := liftToOpens_comp_ι (dQ.fibreIso T f).hom (hψ.hom T f).relativeMapDomain
        (by rw [hdom T f, Scheme.Hom.preimage_top])
      rw [← IsIso.eq_comp_inv] at e
      rw [e]
      infer_instance
    rw [W.cancel_left_of_respectsIso, W.cancel_right_of_respectsIso]
    exact hW T f
  refine MorphismProperty.relative.of_exists fun T g => ?_
  let f : yoneda.obj T ⟶ X := g ≫ πP
  let s : T ⟶ dP.fibre T f :=
    (dP.pointEquivOver T f (𝟙 T) ⟨g, by rw [CategoryTheory.Functor.map_id, Category.id_comp]⟩).1
  have hs : yoneda.map s ≫ dP.fibreToSpace T f = g := dP.map_pointEquivOver T f (𝟙 T) ⟨g, _⟩
  refine ⟨pullback s (hψ.fibreMap hdom T f),
    yoneda.map (pullback.snd s (hψ.fibreMap hdom T f)) ≫ hψ.fibreToDomain hdom T f,
    pullback.fst s (hψ.fibreMap hdom T f), ?_, ?_⟩
  · simpa only [hs] using
      ((IsPullback.of_hasPullback s (hψ.fibreMap hdom T f)).flip.map yoneda).paste_horiz
        (hψ.isPullback_fibreToDomain hdom T f)
  · exact (W.inverseImage (BigFppfOver.toScheme B S hS)).pullback_fst _ _ (hρ T f)

omit hdom in
/-- **Stacks 085H (2): `r_ψ : U(ψ) ⟶ P` is a closed immersion of algebraic spaces** when every
restriction of `ψ` to a scheme point of the base is surjective in all large degrees. Its source
is all of `Q` by `relativeMapSubfunctor_eq_top_of_eventually_epi`. -/
theorem isClosedImmersion_relativeMapSpaceHom
    (hsurj : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      ∀ᶠ d : ℕ in atTop, Epi ((hψ.hom T f).app (d : ℤ))) :
    IsClosedImmersion B S hS hψ.relativeMapSpaceHom :=
  hψ.presheaf_relativeMapSpaceHom
    (fun T f => relativeMapDomain_eq_top_of_eventually_epi (hψ.hom T f) (hsurj T f))
    @AlgebraicGeometry.IsClosedImmersion
    (fun T f => isClosedImmersion_relativeMapHom_of_eventually_epi (hψ.hom T f) (hsurj T f))

end RelativeProjHomPoints

end AlgebraicGeometry.Space

end
