module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealClosedImmersionCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsLargeSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterionSupplement

/-!
# The global morphism to the spectrum of a presenting ring (Stacks 0AIC)

Let `A` be a weakly admissible topological ring and let the fppf sheaf `X` over `S` be the
colimit of the spectra of the quotients of `A` by its weak ideals of definition — condition
(1) of **Stacks 0AIC**. This file produces the morphism `X ⟶ Spec A` of condition (2) *globally*,
as an `AlgebraicGeometry.FormalSpace.MapToScheme`: a morphism of schemes `T ⟶ Spec A` for
**every** object `T` of the site and every `T`-point of `X`, natural in `T`. With it, condition
(1) yields the library's
`AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`, and — through the
arrow (4) ⟹ (1) of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing` — condition (4) yields it
too.

## Main definitions

* `FormalSpace.weakIdealStageToSpec`: the morphism from a stage of a weak-ideal presentation to
  `Spec A`.
* `FormalSpace.toBasePoints`: the structure morphism of the site, read as a morphism from an
  arbitrary fppf sheaf to the functor of points of the base.
* `FormalSpace.weakIdealToSpecPoints`: the morphism of sheaves `X ⟶ Spec A` attached to a
  weak-ideal presentation.
* `FormalSpace.mapToSchemeOfWeakIdealColimitPresentation`: the same morphism in the
  Yoneda-transposed form that condition (2) asks for.

## Main results

* `FormalSpace.hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation`:
  **Stacks 0AIC**, condition (1) implies condition (2).
* `FormalSpace.hasSchemeClosedImmersionCriterion_of_weakIdealColimitPresentation`:
  **Stacks 0AIC**, condition (1) implies condition (3).
* `FormalSpace.hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation` and
  `FormalSpace.hasSchemeClosedImmersionCriterion_of_hasSomeSurjectivePresentation`:
  **Stacks 0AIC**, condition (4) implies conditions (2) and (3).

## Implementation notes

*Why a global morphism needs descent.* A `T`-point of `X` for an arbitrary object `T` of the
site is only *locally* given by a morphism to a stage of the presentation, since `X` is the
colimit of the stages taken in **sheaves**, that is the sheafification of the colimit of
presheaves; the locality is fppf, not even Zariski. So there is no factorisation of a point
through a stage to read a morphism `T ⟶ Spec A` off, and the family has to be assembled from
local factorisations. That is exactly what
`AlgebraicGeometry.FormalSpace.isClosedImmersion_toSpec_of_weakIdealColimitPresentation` cannot
do: it produces a morphism only where a factorisation exists, namely at a closed immersion of
an affine scheme.

*How the gluing is organised.* The local factorisations are not glued by hand. The functor of
points of `Spec A`, which is a scheme of **arbitrary size** — condition (1) bounds the size only
of the quotients of `A`, and site-membership of `Spec A` is not derivable from it — is an fppf
sheaf on the site by `AlgebraicGeometry.Space.isSheaf_largeSchemePointsPresheaf`, which is
affine fpqc descent with no size restriction. A sheaf receives a morphism from a colimit of
sheaves as soon as it receives a compatible family from the stages, and a morphism from the
sheafified representable of a stage is a *section over that stage*, by Yoneda's lemma for
sheaves `CategoryTheory.Sheaf.sectionEquiv`. The compatible family is therefore the family of
morphisms of schemes `Spec (A ⧸ K) ⟶ Spec A`, and the universal property of the colimit performs
the descent: every amalgamation of local factorisations that a hand-written argument would
produce is the value of the resulting morphism of sheaves. No size bound and no restriction of
`T` to the affine or quasi-compact case enters.

*No structure morphism on `Spec A`.* Conditions (2) and (3) of Stacks 0AIC require no morphism
`Spec A ⟶ S`, and the arrows into them proved here assume none. That is not a convenience: the
library's `AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` records only the
structure morphisms of the quotients, from which a morphism `Spec A ⟶ S` cannot be recovered —
the stages sit inside `Spec A` by closed immersions and admit no retraction — and the presenting
ring produced from condition (4) by
`AlgebraicGeometry.FormalSpace.exists_isPresentingRing_of_hasSomeSurjectivePresentation` is the
inverse limit of the stage rings, whose spectrum has no morphism to a non-affine `S` at all. So
a condition (2) carrying a structure morphism would be strictly stronger than the source's and
would have no arrow from condition (4). Condition (2) is obtained here with `A` itself as the
witness, and the statement that the global morphism does lie over `S` when a compatible
`Spec A ⟶ S` happens to be given is kept separately as
`AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints_comp_map`.

*Faithfulness of the closed-immersion clause.* The criterion of condition (2) is discharged by
`isClosedImmersion_toSpec_of_weakIdealColimitPresentation`: the morphism of schemes that clause
exhibits at a closed immersion `T ⟶ X` of an affine scheme of the site is *the same* morphism as
the value of the global family there, because the value of the global family on a point that
does factor through a stage is read off from that factorisation, which is
`AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints_comp_stage`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of the site, read as a morphism of sheaves from an arbitrary fppf
sheaf `F` over `S` to the functor of points of `S`: a `T`-point of `F` is sent to the structure
morphism of `T`. It is natural because the structure morphism of an object of the slice factors
the structure morphism of its target. -/
def toBasePoints (F : FppfSheaf B S hS) :
    F ⟶ (Space.largeSchemePoints B S hS).obj S :=
  ObjectProperty.homMk
    { app := fun T => ↾fun _ : F.obj.obj T =>
        Space.largeSchemePointsSection B S hS (B.inclusion.map T.unop.hom)
      naturality := by
        intro U V f
        ext x
        refine ULift.ext ?_
        change B.inclusion.map V.unop.hom =
          B.inclusion.map f.unop.left ≫ B.inclusion.map U.unop.hom
        rw [← B.inclusion.map_comp, Over.w f.unop] }

/-- The section of the functor of points of the base cut out by a point of a sheaf is the
structure morphism of the object the point lives over. -/
theorem sectionEquiv_comp_toBasePoints {F : FppfSheaf B S hS} (T : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ F) :
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (g ≫ toBasePoints B S hS F)).down =
      B.inclusion.map T.hom := by
  rw [Sheaf.sectionEquiv_comp]
  rfl

/-- Postcomposing a morphism into the functor of points of a scheme with a morphism of schemes
postcomposes the morphism of schemes attached to every point. -/
theorem sectionEquiv_comp_largeSchemePoints_map {Z Z' : Scheme.{u}} (f : Z ⟶ Z')
    {F : FppfSheaf B S hS} (Φ : F ⟶ (Space.largeSchemePoints B S hS).obj Z)
    (T : BigFppfOver B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ F) :
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (g ≫ Φ ≫ (Space.largeSchemePoints B S hS).map f)).down =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (g ≫ Φ)).down ≫ f := by
  rw [← Category.assoc, Sheaf.sectionEquiv_comp]
  rfl

end

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A]

/-- The morphism from a stage of a weak-ideal presentation to the spectrum of the presenting
ring: the identification of the stage with `Spec (A ⧸ K)`, followed by the morphism of spectra
induced by the quotient homomorphism `A → A ⧸ K`. -/
noncomputable abbrev weakIdealStageToSpec {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) (K : WeakIdeals A) :
    (BigAffineFppf.toScheme B S hS).obj (P.diagram.obj K) ⟶ Spec (.of A) :=
  (P.quotientIso K).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1))

/-- The morphisms from the stages of a weak-ideal presentation to `Spec A` are compatible with
the transition morphisms of the presentation: the transition morphisms are induced by the
quotient homomorphisms, which are compatible with the projections to `A`. -/
theorem map_weakIdealStageToSpec {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) {J K : WeakIdeals A} (f : J ⟶ K) :
    (BigAffineFppf.toScheme B S hS).map (P.diagram.map f) ≫
        weakIdealStageToSpec B S hS A P K =
      weakIdealStageToSpec B S hS A P J := by
  have hle : (K.1 : Ideal A) ≤ J.1 := leOfHom f
  rw [weakIdealStageToSpec, ← Category.assoc, P.quotientIso_natural f, Category.assoc,
    ← Spec.map_comp]
  refine congrArg (fun g => (P.quotientIso J).hom ≫ Spec.map g) ?_
  exact congrArg CommRingCat.ofHom (Ideal.Quotient.factor_comp_mk hle)

/-- The cocone on the stages of a weak-ideal presentation with point the functor of points of
`Spec A`: its component at the stage indexed by `K` is the morphism of sheaves corresponding,
under Yoneda's lemma for sheaves, to the morphism of schemes `Spec (A ⧸ K) ⟶ Spec A`. -/
@[reducible] noncomputable def weakIdealSpecCocone {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) :
    Cocone (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) where
  pt := (Space.largeSchemePoints B S hS).obj (Spec (.of A))
  ι :=
    { app := fun K =>
        show _ ⟶ (Space.largeSchemePoints B S hS).obj (Spec (.of A)) from
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
            (Space.largeSchemePointsSection B S hS (weakIdealStageToSpec B S hS A P K))
      naturality := by
        intro J K f
        simp only [Functor.const_obj_map, Functor.comp_map]
        rw [← Sheaf.sectionEquiv_symm_map]
        refine congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm ?_
        exact ULift.ext (map_weakIdealStageToSpec B S hS A P f) }

/-- The morphism of sheaves `X ⟶ Spec A` attached to a weak-ideal presentation of `X`: the
morphism out of the colimit of the stages determined by the morphisms `Spec (A ⧸ K) ⟶ Spec A`.

Its existence is the descent step: the target is the functor of points of a scheme of arbitrary
size, which is an fppf sheaf on the site, so the universal property of the colimit of sheaves
glues the morphisms from the stages into a morphism defined on all of `X`. -/
noncomputable def weakIdealToSpecPoints {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) :
    X ⟶ (Space.largeSchemePoints B S hS).obj (Spec (.of A)) :=
  P.colimitIso.hom ≫ colimit.desc _ (weakIdealSpecCocone B S hS A P)

/-- The tautological point of `X` over the stage indexed by `K`: the colimit injection of that
stage, read through the identification of the colimit with `X`. -/
noncomputable abbrev weakIdealStagePoint {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) (K : WeakIdeals A) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)) ⟶ X :=
  colimit.ι (P.diagram ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) K ≫ P.colimitIso.inv

/-- The value of `AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints` at the tautological point
of a stage is the morphism of that stage to `Spec A`; this is how the global morphism is read
off from a factorisation through a stage. -/
theorem weakIdealToSpecPoints_comp_stage {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) (K : WeakIdeals A) :
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
        (weakIdealStagePoint B S hS A P K ≫ weakIdealToSpecPoints B S hS A P)).down =
      weakIdealStageToSpec B S hS A P K := by
  have h : weakIdealStagePoint B S hS A P K ≫ weakIdealToSpecPoints B S hS A P =
      (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
        (Space.largeSchemePointsSection B S hS (weakIdealStageToSpec B S hS A P K)) := by
    rw [weakIdealStagePoint, weakIdealToSpecPoints, Category.assoc,
      P.colimitIso.inv_hom_id_assoc]
    exact colimit.ι_desc _ K
  rw [h]
  exact congrArg (fun y => ULift.down y)
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply _)

/-- The morphism `X ⟶ Spec A` of a weak-ideal presentation lies over `S` as soon as the
morphism `Spec A ⟶ S` restricts on every stage to the structure morphism of that stage. Both
sides are morphisms out of the colimit of the stages, so it is enough to compare them there. -/
theorem weakIdealToSpecPoints_comp_map {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) (fA : Spec (.of A) ⟶ S)
    (hfA : ∀ K : WeakIdeals A, weakIdealStageToSpec B S hS A P K ≫ fA =
      B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K)).hom) :
    weakIdealToSpecPoints B S hS A P ≫ (Space.largeSchemePoints B S hS).map fA =
      toBasePoints B S hS X := by
  refine (cancel_epi P.colimitIso.inv).1 (colimit.hom_ext fun K => ?_)
  rw [← Category.assoc (colimit.ι _ K) P.colimitIso.inv
      (weakIdealToSpecPoints B S hS A P ≫ (Space.largeSchemePoints B S hS).map fA),
    ← Category.assoc (colimit.ι _ K) P.colimitIso.inv (toBasePoints B S hS X)]
  refine (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).injective (ULift.ext ?_)
  rw [sectionEquiv_comp_largeSchemePoints_map, sectionEquiv_comp_toBasePoints,
    weakIdealToSpecPoints_comp_stage]
  exact hfA K

end

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

/-- The Yoneda-transposed form of `AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints`: the
family which sends a `T`-point of `X`, for an arbitrary object `T` of the site, to a morphism of
schemes `T ⟶ Spec A`, natural in `T`.

No structure morphism `Spec A ⟶ S` is involved, and none is available: the stages of the
presentation sit inside `Spec A` as closed subschemes and admit no retraction, so a morphism
`Spec A ⟶ S` cannot be recovered from the structure morphisms of the quotients that
`AlgebraicGeometry.FormalSpace.WeakIdealColimitPresentation` records. Condition (2) of Stacks
0AIC asks for none, and this family is already the whole of its datum. -/
noncomputable def mapToSchemeOfWeakIdealColimitPresentation {X : FppfSheaf B S hS}
    (P : WeakIdealColimitPresentation B S hS A X) :
    MapToScheme B S hS (Spec (.of A)) X where
  app T g := (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
    (g ≫ weakIdealToSpecPoints B S hS A P)).down
  app_naturality T T' u g := by
    have h := Sheaf.sectionEquiv_map_comp (BigFppfOver.topology B S hS) u
      (g ≫ weakIdealToSpecPoints B S hS A P)
    rw [← Category.assoc] at h
    exact congrArg ULift.down h

/-- **The closed-immersion clause of condition (2) of Stacks 0AIC, with the ring named.** Let
`A` be a weakly admissible topological ring presenting `X`. Then every closed immersion of an
affine scheme `T` of the site into `X` composes with the canonical morphism `X ⟶ Spec A` of
`AlgebraicGeometry.FormalSpace.mapToSchemeOfWeakIdealColimitPresentation` to a closed immersion
of schemes, so that `A` surjects onto `Γ(T, 𝒪)`.

This is the content of
`AlgebraicGeometry.FormalSpace.hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation`
with `A` kept in the statement rather than bound by the existential of
`AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`, which is what a
consumer needing the *ideals* of the stages of a presentation — the kernels of those surjections
— has to have. The morphism is read off from a factorisation through a stage, which is
`AlgebraicGeometry.FormalSpace.isClosedImmersion_toSpec_of_weakIdealColimitPresentation`, and
agrees there with the value of the global family by
`AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints_comp_stage`. -/
theorem isClosedImmersion_app_mapToSchemeOfWeakIdealColimitPresentation
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) (T : BigAffineFppf B S hS)
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj T) ⟶ X)
    (hg : IsClosedImmersionInto B S hS g) :
    IsClosedImmersion ((mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app
      ((BigAffineFppf.inclusion B S hS).obj T) g) := by
  obtain ⟨K, c, hfac, hclosed⟩ :=
    (isClosedImmersion_toSpec_of_weakIdealColimitPresentation B S hS A hA hset P).2 T g hg
  -- The value of the global family at `g` is the morphism the factorisation exhibits.
  have hval : (mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app
        ((BigAffineFppf.inclusion B S hS).obj T) g =
      (BigAffineFppf.toScheme B S hS).map c ≫ weakIdealStageToSpec B S hS A P K := by
    have h := (mapToSchemeOfWeakIdealColimitPresentation B S hS A P).app_naturality
      ((BigAffineFppf.inclusion B S hS).obj (P.diagram.obj K))
      ((BigAffineFppf.inclusion B S hS).obj T)
      ((BigAffineFppf.inclusion B S hS).map c) (weakIdealStagePoint B S hS A P K)
    rw [hfac] at h
    rw [h]
    change _ ≫ (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
      (weakIdealStagePoint B S hS A P K ≫ weakIdealToSpecPoints B S hS A P)).down = _
    rw [weakIdealToSpecPoints_comp_stage]
    rfl
  rw [hval]
  exact hclosed

/-- **Stacks 0AIC, condition (1) implies condition (2).** Let `A` be a weakly admissible
topological ring and let the fppf sheaf `X`, satisfying the set-theoretic condition of
Stacks 0AIS, be the colimit of the spectra of the quotients of `A` by its weak ideals of
definition. Then `X` is an affine formal algebraic space, and there are a ring and a morphism of
sheaves from `X` to its spectrum such that every closed immersion of an affine scheme of the
site into `X` composes to a closed immersion of schemes; the witnesses are `A` itself and
`AlgebraicGeometry.FormalSpace.weakIdealToSpecPoints`.

This is the library's `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterionMapToSpec`:
the morphism to `Spec A` is given at every object of the site, not only at those carrying a closed
immersion into `X`. The implication is unconditional — no morphism `Spec A ⟶ S` and no
compatibility with the structure morphisms of the stages is assumed — because condition (2),
like the source's, asks for none. -/
@[stacks 0AIC "(1) implies (2)"]
theorem hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS X :=
  ⟨(isClosedImmersion_toSpec_of_weakIdealColimitPresentation B S hS A hA hset P).1, .of A,
    mapToSchemeOfWeakIdealColimitPresentation B S hS A P,
    isClosedImmersion_app_mapToSchemeOfWeakIdealColimitPresentation B S hS A hA hset P⟩

/-- **Stacks 0AIC, condition (1) implies condition (3).** Condition (1) gives condition (2), and
a scheme closed-immersed in an affine formal algebraic space is affine, so the criterion extends
from the affine schemes of the site to all of them. -/
@[stacks 0AIC "(1) implies (3)"]
theorem hasSchemeClosedImmersionCriterion_of_weakIdealColimitPresentation
    (hA : TopologicalRing.IsWeaklyAdmissible A) {X : FppfSheaf B S hS}
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (P : WeakIdealColimitPresentation B S hS A X) :
    HasSchemeClosedImmersionCriterionMapToSpec B S hS X :=
  HasAffineClosedImmersionCriterionMapToSpec.hasSchemeClosedImmersionCriterionMapToSpec B S hS
    (hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation B S hS A hA hset P)

end

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AIC, condition (4) implies condition (2).** An affine formal algebraic space with
*some* presentation by affine thickenings whose section-ring projections are surjective admits a
ring `A` and a morphism `X ⟶ Spec A` through which every closed immersion of an affine scheme of
the site into `X` composes to a closed immersion of schemes.

The ring is the one condition (4) produces, namely the inverse limit of the section rings of the
presentation, and the morphism is the global family built above. No structure morphism
`Spec A ⟶ S` is involved anywhere, which is what makes this arrow available: that limit carries
none, so a condition (2) demanding one would have no arrow out of condition (4). -/
@[stacks 0AIC "(4) implies (2)"]
theorem hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation
    {X : FppfSheaf B S hS} (hX : HasSomeSurjectivePresentation B S hS X) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS X := by
  obtain ⟨A, instCR, instTS, instTR, instLT, hA, ⟨P⟩⟩ :=
    exists_isPresentingRing_of_hasSomeSurjectivePresentation B S hS hX
  let : CommRing A := instCR
  let : TopologicalSpace A := instTS
  let : IsTopologicalRing A := instTR
  let : IsLinearTopology A A := instLT
  exact hasAffineClosedImmersionCriterion_of_weakIdealColimitPresentation B S hS A hA hX.1.1 P

/-- **Stacks 0AIC, condition (4) implies condition (3).** Condition (4) gives condition (2), and
a scheme closed-immersed in an affine formal algebraic space is affine, so the criterion extends
from the affine schemes of the site to all of them. -/
@[stacks 0AIC "(4) implies (3)"]
theorem hasSchemeClosedImmersionCriterion_of_hasSomeSurjectivePresentation
    {X : FppfSheaf B S hS} (hX : HasSomeSurjectivePresentation B S hS X) :
    HasSchemeClosedImmersionCriterionMapToSpec B S hS X :=
  HasAffineClosedImmersionCriterionMapToSpec.hasSchemeClosedImmersionCriterionMapToSpec B S hS
    (hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS hX)

/-- **Stacks 0AIC, condition (5) implies condition (2).** Condition (5) gives condition (4) by
instantiating its quantifier at the presentation an affine formal algebraic space comes with,
and condition (4) gives condition (2). -/
@[stacks 0AIC "(5) implies (2)"]
theorem hasAffineClosedImmersionCriterion_of_hasAllSurjectivePresentations
    {X : FppfSheaf B S hS} (hX : HasAllSurjectivePresentations B S hS X) :
    HasAffineClosedImmersionCriterionMapToSpec B S hS X :=
  hasAffineClosedImmersionCriterion_of_hasSomeSurjectivePresentation B S hS
    (hX.hasSomeSurjectivePresentation B S hS)

end

end AlgebraicGeometry.FormalSpace

end
