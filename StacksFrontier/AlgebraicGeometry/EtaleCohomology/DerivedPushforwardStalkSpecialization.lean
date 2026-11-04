module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity

/-!
# Specialization and the stalk of a direct image

Let `f : X ⟶ S` be a morphism of schemes, let `s` be a geometric point of `S` and let `t` be a
geometric point of the strict henselization `Spec(𝒪^{sh}_{S,s})`, with structure morphism
`p : Spec(𝒪^{sh}_{S,s}) ⟶ S`. The specialization morphism of strict henselizations of Stacks
0GJ4 is a morphism `c : Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ Spec(𝒪^{sh}_{S,s})` over `S`, and base changing
`f` along it gives a morphism `id_X × c` between the two base changes
`X ×_S Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ X ×_S Spec(𝒪^{sh}_{S,s})` over `X`.

This file builds that morphism and proves that the square

```
(f_*F)_s ---------- sp ----------> (f_*F)_{t ≫ p}
   |                                     |
   v                                     v
Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F) --> Γ(X ×_S Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹F)
```

of abelian étale sheaves commutes, the verticals being the map on sheaves underlying the first
canonical map of Stacks 0GIX and the bottom arrow being restriction of sections along
`id_X × c`. This is Stacks 0GJ8 on abelian sheaves; the statement of 0GJ8 itself is about the
unbounded derived category, and what is still missing for it is recorded below.

## Main definitions

* `AlgebraicGeometry.strictHenselizationBaseChangeSpecializationMap` — the morphism `id_X × c`
  of base changes.
* `AlgebraicGeometry.strictHenselizationBaseChangeEtaleLift` — the canonical morphism
  `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X ×_S W` over `X` attached to an étale neighbourhood `(W, v)` of
  `s`.
* `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift` — the identification of a
  composite of two derived inverse images with a third, lifted through `DerivedCategory.Qh` so
  that its effect on the image of a complex is computable.
* `AlgebraicGeometry.strictHenselizationSectionsSpecialization` — the bottom arrow of Stacks
  0GJ8: the map `RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹K)`
  given by pullback along `id_X × c`.

## Main results

* `AlgebraicGeometry.specializationMorphism_comp` and
  `AlgebraicGeometry.geometricPointToStrictHenselization_comp_specializationMorphism` — the two
  properties characterizing the specialization morphism of strict henselizations.
* `AlgebraicGeometry.specializationMorphism_comp_neighborhoodLift` — the specialization morphism
  of strict henselizations is compatible with the canonical morphisms into the étale
  neighbourhoods of the two points.
* `Stacks.Sites.sectionsPullbackComparison_id_comp_counit` — the comparison on sections over `U`
  along the identity of `G.obj U`, applied to a direct image and followed by the counit, is the
  identity.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_eq_unit_comp` — restriction of sections
  over an étale object `W` of `S` to global sections of an inverse image on a scheme `T` over
  `X` factors as the unit of the inverse-image/direct-image adjunction for `f : X ⟶ S` over `W`,
  followed by restriction of sections over the base change `X ×_S W`.
* `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber` — the map
  on sheaves of Stacks 0GIX, on germs: a germ at `s` of a section of `f_*F` over `(W, v)`, which
  is a section of `F` over `X ×_S W`, goes to its restriction along
  `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X ×_S W`.
* `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_comp_sectionsRestrictionAb`
  — **the square above**.

## Implementation notes

*Why the germ description is the whole content.* Both sides of the square are maps out of the
stalk at `s` of `f_*F`, which is the colimit of the sections of `f_*F` over the étale
neighbourhoods of `s`, so they agree as soon as they agree on germs. On the germ of a section
over `(W, v)` both sides are restriction along a morphism
`X ×_S Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ X ×_S W`, and the two morphisms coincide because `c` carries the
canonical morphism `Spec(𝒪^{sh}_{S,s}) ⟶ W` to the canonical morphism
`Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ W` for the specialized lift; that is
`AlgebraicGeometry.specializationMorphism_comp_neighborhoodLift`, and it holds by the uniqueness
of those morphisms.

Getting to the germ description of
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` is the work: that map is
built from `AlgebraicGeometry.etaleStalkToSectionsAb` followed by the composition isomorphism for
inverse images and the counit of the adjunction for `f`, and the germ description says that the
three together are plain restriction of sections over the étale object `X ×_S W` of `X`. The
composition isomorphism is handled by `Stacks.Sites.unit_comp_leftAdjointUniq_app` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/StalkSectionsTransitivity.lean`, which is what
computes it on sections, and the counit by the triangle identity of the adjunction read on
sections.

*Why the derived composition isomorphism is built here.* The bottom arrow of 0GJ8 needs an
identification of `(id_X × c)⁻¹p⁻¹K` with the inverse image of `K` along the projection of the
second base change. The library's general such identification,
`CategoryTheory.Functor.mapDerivedCategoryCompIso`
(`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardClosedImmersion.lean`), is a lift of
the degreewise isomorphism through `DerivedCategory.Q`, and nothing computes its effect on an
object `DerivedCategory.Qh.obj J` of the derived category; the bottom arrow built from it is
therefore opaque. `Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift` lifts the same
degreewise isomorphism through `DerivedCategory.Qh` instead, which is the localization the units
of the derivations are indexed by, and so comes with
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app`.

*What is still missing for Stacks 0GJ8.* The source states the square for an object `K` of
`D⁺(X_étale)`, with the verticals the maps of Stacks 0GIX on unbounded derived categories,
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`, the top arrow the
specialization map on derived stalks,
`AlgebraicGeometry.smallEtaleDerivedSpecializationStalkAb`, and the bottom arrow
`AlgebraicGeometry.strictHenselizationSectionsSpecialization`. Both sides are transformations out
of the right derived functor `smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom`,
so `CategoryTheory.Functor.rightDerived_ext` reduces the square to an identity of the two
comparisons on the homotopy category, which the following reduce further, in this order:
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_fac_app` at `s` and at
`t ≫ p`; the naturality of the specialization map on derived stalks at the unit of the derivation
of direct image; `Stacks.DerivedFunctor.exactDerivedDescUnit_app`;
the naturality of `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction` at
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`;
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_fac_app`;
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app`, whose three
`mapDerivedCategoryFactorsh` factors cancel against those just produced; and the naturality of
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsUnit` at
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`. What is left after all of that is the
degreewise statement: the image under `CategoryTheory.NatTrans.mapHomotopyCategory` of the square
proved here, reconciled with the `CategoryTheory.Functor.mapHomotopyCategoryCompIso` factors of
`Stacks.DerivedFunctor.mapHomotopyCategoryOfComp`. That last identity is not proved here, so no
0GJ8 is claimed.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
* [Stacks Project, Tag 0GJ8](https://stacks.math.columbia.edu/tag/0GJ8)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-! ### The specialization morphism of strict henselizations -/

section Morphism

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- The specialization morphism of strict henselizations lies over `S`. -/
theorem specializationMorphism_comp :
    specializationMorphism B S hS s t ≫ strictHenselizationToBase B S hS s =
      strictHenselizationToBase B S hS (t.map (strictHenselizationToBase B S hS s)) :=
  (existsUnique_specializationMorphism B S hS s t).exists.choose_spec.1

/-- The specialization morphism of strict henselizations carries the canonical geometric point of
its source to the given geometric point of the strict henselization at `s`. -/
theorem geometricPointToStrictHenselization_comp_specializationMorphism :
    geometricPointToStrictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s)) ≫
        specializationMorphism B S hS s t = t.hom :=
  (existsUnique_specializationMorphism B S hS s t).exists.choose_spec.2

/-- The specialization morphism of strict henselizations is compatible with the canonical
morphisms into the étale neighbourhoods: composing it with the morphism from the strict
henselization at `s` into an étale neighbourhood `(W, v)` of `s` gives the morphism from the
strict henselization at the specialized point into `W` at the specialized lift. -/
theorem specializationMorphism_comp_neighborhoodLift (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    specializationMorphism B S hS s t ≫ strictHenselizationNeighborhoodLift B S hS s W v =
      strictHenselizationNeighborhoodLift B S hS
        (t.map (strictHenselizationToBase B S hS s)) W
        (specializationEtaleNeighborhoodLift B S hS s t W v) :=
  strictHenselizationNeighborhoodLift_eq B S hS
    (t.map (strictHenselizationToBase B S hS s)) W
    (specializationEtaleNeighborhoodLift B S hS s t W v) _
    ((Category.assoc _ _ _).trans
      ((congrArg (specializationMorphism B S hS s t ≫ ·)
          (strictHenselizationNeighborhoodLift_comp B S hS s W v)).trans
        (specializationMorphism_comp B S hS s t)))
    (by rw [← Category.assoc, geometricPointToStrictHenselization_comp_specializationMorphism,
      specializationEtaleNeighborhoodLift_left])

end Morphism

/-! ### The base change of a morphism along the specialization morphism -/

section BaseChange

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The morphism `id_X × c` of base changes to the two strict henselizations, where `c` is the
specialization morphism of strict henselizations of Stacks 0GJ4. -/
def strictHenselizationBaseChangeSpecializationMap :
    strictHenselizationBaseChange B hS f (t.map (strictHenselizationToBase B S hS s)) ⟶
      strictHenselizationBaseChange B hS f s :=
  pullback.lift
    (strictHenselizationBaseChangeToSource B hS f
      (t.map (strictHenselizationToBase B S hS s)))
    (strictHenselizationBaseChangeToStrictHenselization B hS f
        (t.map (strictHenselizationToBase B S hS s)) ≫
      specializationMorphism B S hS s t)
    (pullback.condition.trans
      ((congrArg (fun y : strictHenselization B S hS
              (t.map (strictHenselizationToBase B S hS s)) ⟶ S =>
            strictHenselizationBaseChangeToStrictHenselization B hS f
              (t.map (strictHenselizationToBase B S hS s)) ≫ y)
          (specializationMorphism_comp B S hS s t)).symm.trans
        (Category.assoc _ _ _).symm))

/-- The morphism `id_X × c` lies over `X`. -/
theorem strictHenselizationBaseChangeSpecializationMap_comp_toSource :
    strictHenselizationBaseChangeSpecializationMap B hS f s t ≫
        strictHenselizationBaseChangeToSource B hS f s =
      strictHenselizationBaseChangeToSource B hS f
        (t.map (strictHenselizationToBase B S hS s)) :=
  pullback.lift_fst _ _ _

/-- The morphism `id_X × c` is the specialization morphism on the second projections. -/
theorem strictHenselizationBaseChangeSpecializationMap_comp_toStrictHenselization :
    strictHenselizationBaseChangeSpecializationMap B hS f s t ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f s =
      strictHenselizationBaseChangeToStrictHenselization B hS f
          (t.map (strictHenselizationToBase B S hS s)) ≫
        specializationMorphism B S hS s t :=
  pullback.lift_snd _ _ _

end BaseChange

end AlgebraicGeometry

namespace Stacks.Sites

/-- **The unit over the image of an object cancels the counit.** For an
inverse-image/direct-image adjunction of sites, the comparison on sections over `U` along the
identity of `G.obj U`, applied to a direct image and followed by the counit on sections over
`G.obj U`, is the identity. This is the triangle identity of the adjunction, read on sections. -/
theorem sectionsPullbackComparison_id_comp_counit {C : Type*} [Category C] {D : Type*}
    [Category D] (G : C ⥤ D) (A : Type*) [Category A] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [G.IsContinuous J K] {P : Sheaf J A ⥤ Sheaf K A}
    (adj : P ⊣ G.sheafPushforwardContinuous A J K) (U : C) (F : Sheaf K A) :
    (sectionsPullbackComparison G A J K adj (𝟙 (G.obj U))).app
          ((G.sheafPushforwardContinuous A J K).obj F) ≫
        (adj.counit.app F).hom.app (op (G.obj U)) =
      𝟙 (((G.sheafPushforwardContinuous A J K).obj F).obj.obj (op U)) := by
  have h := congrArg
    (fun β : (G.sheafPushforwardContinuous A J K).obj F ⟶
        (G.sheafPushforwardContinuous A J K).obj F => β.hom.app (op U))
    (adj.right_triangle_components F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.sheafPushforwardContinuous_map_hom_app] at h
  have e : (P.obj ((G.sheafPushforwardContinuous A J K).obj F)).obj.map (𝟙 (G.obj U)).op =
      𝟙 ((P.obj ((G.sheafPushforwardContinuous A J K).obj F)).obj.obj (op (G.obj U))) :=
    (congrArg (P.obj ((G.sheafPushforwardContinuous A J K).obj F)).obj.map op_id).trans
      ((P.obj ((G.sheafPushforwardContinuous A J K).obj F)).obj.map_id (op (G.obj U)))
  have step : (sectionsPullbackComparison G A J K adj (𝟙 (G.obj U))).app
        ((G.sheafPushforwardContinuous A J K).obj F) =
      (adj.unit.app ((G.sheafPushforwardContinuous A J K).obj F)).hom.app (op U) ≫ 𝟙 _ :=
    congrArg
      (fun y => (adj.unit.app ((G.sheafPushforwardContinuous A J K).obj F)).hom.app (op U) ≫ y) e
  rwa [step, Category.comp_id]

end Stacks.Sites

namespace Stacks.EtaleCohomology

/-! ### Restriction of sections over an étale object of the base -/

/-- Transitivity of a comparison on sections is unchanged by conjugating the sections functor of
the final target with an isomorphism, for instance the identification of global sections with
sections over a terminal object. This is the whiskering bookkeeping of
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_eq_unit_comp`. -/
private theorem whiskeredComparison_fac {S₁ : Type*} [Category S₁] {S₂ : Type*} [Category S₂]
    {S₃ : Type*} [Category S₃] {A : Type*} [Category A] {P₁ : S₁ ⥤ S₂} {P₂ : S₂ ⥤ S₃}
    {P₃ : S₁ ⥤ S₃} (e : P₁ ⋙ P₂ ≅ P₃) {Q : S₁ ⥤ A} {R₂ : S₂ ⥤ A} {R₃ Γ₃ : S₃ ⥤ A}
    (ι₃ : Γ₃ ≅ R₃) (a₁ : Q ⟶ P₁ ⋙ R₂) (a₂ : R₂ ⟶ P₂ ⋙ R₃) (a₃ : Q ⟶ P₃ ⋙ R₃)
    (ha : a₁ ≫ Functor.whiskerLeft P₁ a₂ ≫ Functor.whiskerRight e.hom R₃ = a₃) :
    a₁ ≫ Functor.whiskerLeft P₁ (a₂ ≫ Functor.whiskerLeft P₂ ι₃.inv) ≫
        Functor.whiskerRight e.hom Γ₃ =
      a₃ ≫ Functor.whiskerLeft P₃ ι₃.inv := by
  subst ha
  ext F
  simp

/-- A three-fold composite rewritten through three factorizations of its constituents, in an
arbitrary category: the associativity bookkeeping of
`Stacks.EtaleCohomology.smallEtaleBaseChangeLift_comp_baseChangeComp`, separated from its content
because the objects involved are fibre products carrying instance arguments which agree only up
to proof irrelevance. -/
private theorem comp_fst_fac {C : Type*} [Category C] {A B D E H : C} {a : A ⟶ B} {b : B ⟶ D}
    {i : D ⟶ E} {c : B ⟶ H} {d : H ⟶ E} {ρ : A ⟶ H} {r : A ⟶ E} (h₁ : b ≫ i = c ≫ d)
    (h₂ : a ≫ c = ρ) (h₃ : ρ ≫ d = r) :
    (a ≫ b) ≫ i = r := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, h₃]

section Lift

variable {S X T : Scheme.{u}} (f : X ⟶ S) (q : T ⟶ X) (V : S.Etale) (r : T ⟶ V.left)

/-- The morphism of étale objects determined by a section of the base change along `q` of the
base change of `V` along `f`, read through the comparison of the base change along `q ≫ f` with
the composite of the two base changes, is the morphism determined by the section itself. -/
theorem smallEtaleBaseChangeLift_comp_baseChangeComp (hr : r ≫ V.hom = q ≫ f) :
    smallEtaleBaseChangeLift q ((smallEtaleBaseChange f).obj V) (pullback.lift r q hr)
          (by exact pullback.lift_snd _ _ _) ≫
        (smallEtaleBaseChangeComp q f).inv.app V =
      smallEtaleBaseChangeLift (q ≫ f) V r hr :=
  smallEtaleBaseChangeLift_eq (q ≫ f) V r hr _
    (comp_fst_fac (smallEtaleBaseChangeComp_inv_app_left_fst q f V)
      (pullback.lift_fst _ _ _) (pullback.lift_fst r q hr))

/-- **Restriction of sections over an étale object of the base factors through the unit of the
inverse-image/direct-image adjunction.** Let `f : X ⟶ S` and `q : T ⟶ X` be morphisms of schemes
and let `V` be an étale object of `S` with a morphism `r : T ⟶ V.left` over `q ≫ f`. Restricting
a section of an abelian étale sheaf over `V` to a global section of its inverse image on `T`
along `r` is: carrying it by the unit of the adjunction for `f` to a section over the base change
`X ×_S V`, restricting that to a global section of the inverse image on `T` along the induced
morphism, and reading the result through the composition isomorphism for inverse images. -/
theorem smallEtaleSectionsPullbackAb_eq_unit_comp (hr : r ≫ V.hom = q ≫ f) :
    Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange f) Ab.{u + 1}
          (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleAdjunctionAb f)
          (𝟙 ((smallEtaleBaseChange f).obj V)) ≫
        Functor.whiskerLeft (smallEtalePullbackAb f)
          (smallEtaleSectionsPullbackAb q ((smallEtaleBaseChange f).obj V)
            (pullback.lift r q hr) (by exact pullback.lift_snd _ _ _)) ≫
        Functor.whiskerRight (smallEtalePullbackAbCompIso q f).hom
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) =
      smallEtaleSectionsPullbackAb (q ≫ f) V r hr :=
  whiskeredComparison_fac (smallEtalePullbackAbCompIso q f)
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1} (isTerminalEtaleMkId T))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange f) Ab.{u + 1}
      (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleAdjunctionAb f)
      (𝟙 ((smallEtaleBaseChange f).obj V)))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange q) Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology T) (smallEtaleAdjunctionAb q)
      (smallEtaleBaseChangeLift q ((smallEtaleBaseChange f).obj V) (pullback.lift r q hr)
        (by exact pullback.lift_snd _ _ _)))
    (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange (q ≫ f)) Ab.{u + 1}
      (smallEtaleTopology S) (smallEtaleTopology T) (smallEtaleAdjunctionAb (q ≫ f))
      (smallEtaleBaseChangeLift (q ≫ f) V r hr))
    (Stacks.Sites.sectionsPullbackComparison_comp (smallEtaleBaseChange f)
      (smallEtaleBaseChange q) (smallEtaleBaseChange (q ≫ f)) Ab.{u + 1}
      (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleTopology T)
      (smallEtaleAdjunctionAb f) (smallEtaleAdjunctionAb q) (smallEtaleAdjunctionAb (q ≫ f))
      (smallEtalePullbackAbCompIso q f) ((smallEtaleBaseChangeComp q f).symm.hom.app V)
      (fun F => Stacks.Sites.unit_comp_leftAdjointUniq_app (smallEtaleBaseChange f)
        (smallEtaleBaseChange q) (smallEtaleBaseChange (q ≫ f)) Ab.{u + 1}
        (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleTopology T)
        (smallEtaleAdjunctionAb f) (smallEtaleAdjunctionAb q) (smallEtaleAdjunctionAb (q ≫ f))
        (smallEtaleBaseChangeComp q f).symm F V)
      (𝟙 ((smallEtaleBaseChange f).obj V))
      (smallEtaleBaseChangeLift q ((smallEtaleBaseChange f).obj V) (pullback.lift r q hr)
        (by exact pullback.lift_snd _ _ _))
      (smallEtaleBaseChangeLift (q ≫ f) V r hr)
      (((congrArg (fun y => (smallEtaleBaseChangeLift q ((smallEtaleBaseChange f).obj V)
                (pullback.lift r q hr) (by exact pullback.lift_snd _ _ _) ≫ y) ≫
              (smallEtaleBaseChangeComp q f).symm.hom.app V)
            ((smallEtaleBaseChange q).map_id ((smallEtaleBaseChange f).obj V))).trans
        (congrArg (fun y => y ≫ (smallEtaleBaseChangeComp q f).symm.hom.app V)
          (Category.comp_id _))).trans
        (smallEtaleBaseChangeLift_comp_baseChangeComp f q V r hr)))

/-- Restriction of sections over an étale object to global sections of an inverse image is
transported along an equality of the structure morphism to the base by the induced
identification of the inverse-image functors. -/
theorem smallEtaleSectionsPullbackAb_eqToIso_inv {Z T : Scheme.{u}} {p p' : T ⟶ Z} (hp : p' = p)
    (W : Z.Etale) (r : T ⟶ W.left) (hr : r ≫ W.hom = p) :
    smallEtaleSectionsPullbackAb p W r hr ≫
        Functor.whiskerRight
          (eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) hp)).inv
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) =
      smallEtaleSectionsPullbackAb p' W r (hr.trans hp.symm) := by
  subst hp
  simp

end Lift

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-! ### The map from the stalk of a direct image, on germs -/

section Germ

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (V : S.Etale) (w : (Scheme.pointSmallEtale s.hom).fiber.obj V)

/-- The canonical morphism from the base change `X ×_S Spec(𝒪^{sh}_{S,s})` to the base change
`X ×_S W` of an étale neighbourhood `(W, v)` of `s`, over `X`: on the first factor it is the
projection to the strict henselization followed by the canonical morphism into `W`, and on the
second factor it is the projection to `X`. -/
def strictHenselizationBaseChangeEtaleLift :
    strictHenselizationBaseChange B hS f s ⟶ ((smallEtaleBaseChange f).obj V).left :=
  pullback.lift
    (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
      strictHenselizationNeighborhoodLift B S hS s V w)
    (strictHenselizationBaseChangeToSource B hS f s)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun y : strictHenselization B S hS s ⟶ S =>
            strictHenselizationBaseChangeToStrictHenselization B hS f s ≫ y)
          (strictHenselizationNeighborhoodLift_comp B S hS s V w)).trans
        pullback.condition.symm))

/-- The germ-level factorization of the map on sheaves from the stalk of a direct image, before
the counit of the inverse-image/direct-image adjunction is applied: restriction of a section over
an étale neighbourhood `(V, w)` of `s` to global sections on the base change to the strict
henselization, read through the composition isomorphism for inverse images, is the unit of the
adjunction for `f` over `V` followed by restriction of sections over `X ×_S V` along the
canonical morphism. -/
private theorem sectionsPullbackAb_comp_compIso_inv :
    smallEtaleSectionsPullbackAb
          (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
            strictHenselizationToBase B S hS s) V
          (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
            strictHenselizationNeighborhoodLift B S hS s V w)
          (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]) ≫
        Functor.whiskerRight (strictHenselizationBaseChangePullbackAbCompIso B hS f s).inv
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
            Ab.{u + 1}) =
      Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange f) Ab.{u + 1}
          (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleAdjunctionAb f)
          (𝟙 ((smallEtaleBaseChange f).obj V)) ≫
        Functor.whiskerLeft (smallEtalePullbackAb f)
          (smallEtaleSectionsPullbackAb (strictHenselizationBaseChangeToSource B hS f s)
            ((smallEtaleBaseChange f).obj V)
            (strictHenselizationBaseChangeEtaleLift B hS f s V w)
            (by exact pullback.lift_snd _ _ _)) := by
  have hcomp := smallEtaleSectionsPullbackAb_eq_unit_comp f
    (strictHenselizationBaseChangeToSource B hS f s) V
    (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
      strictHenselizationNeighborhoodLift B S hS s V w)
    (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp, pullback.condition])
  have htrans := smallEtaleSectionsPullbackAb_eqToIso_inv
    (pullback.condition (f := f) (g := strictHenselizationToBase B S hS s)) V
    (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
      strictHenselizationNeighborhoodLift B S hS s V w)
    (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])
  have hiso := (Iso.comp_inv_eq (Functor.isoWhiskerRight
      (smallEtalePullbackAbCompIso (strictHenselizationBaseChangeToSource B hS f s) f)
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}))).2 ((Category.assoc _ _ _).trans hcomp).symm
  rwa [strictHenselizationBaseChangePullbackAbCompIso, Iso.trans_inv,
    Functor.whiskerRight_comp, ← Category.assoc, htrans]

/-- **The map from the stalk of a direct image, on germs.** The map on abelian sheaves
`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` of Stacks 0GIX carries the germ at `s` of a
section of `f_*F` over an étale neighbourhood `(V, w)` of `s` — that is, a section of `F` over
the base change `X ×_S V` — to its restriction along the canonical morphism
`X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X ×_S V`.

Germs over all étale neighbourhoods of `s` generate the stalk, so this determines the map. -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (Scheme.pointSmallEtale s.hom).toPresheafFiber V w
          ((smallEtalePushforwardAb f).obj F).obj ≫
        (pushforwardStalkToStrictHenselizationSectionsAb B hS f s).app F =
      (smallEtaleSectionsPullbackAb (strictHenselizationBaseChangeToSource B hS f s)
        ((smallEtaleBaseChange f).obj V)
        (strictHenselizationBaseChangeEtaleLift B hS f s V w)
        (by exact pullback.lift_snd _ _ _)).app F := by
  have hgerm : (Scheme.pointSmallEtale s.hom).toPresheafFiber V w
          ((smallEtalePushforwardAb f).obj F).obj ≫
        (etaleStalkToSectionsAb B S hS s
            (strictHenselizationBaseChangeToStrictHenselization B hS f s)).app
          ((smallEtalePushforwardAb f).obj F) =
      (smallEtaleSectionsPullbackAb
        (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
          strictHenselizationToBase B S hS s) V
        (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
          strictHenselizationNeighborhoodLift B S hS s V w)
        (by rw [Category.assoc, strictHenselizationNeighborhoodLift_comp])).app
        ((smallEtalePushforwardAb f).obj F) :=
    etaleStalkToSectionsAb_toPresheafFiber B S hS s
      (strictHenselizationBaseChangeToStrictHenselization B hS f s)
      ((smallEtalePushforwardAb f).obj F) V w
  have hcomp := congrArg (fun σ => NatTrans.app σ ((smallEtalePushforwardAb f).obj F))
    (sectionsPullbackAb_comp_compIso_inv B hS f s V w)
  have hnat := (smallEtaleSectionsPullbackAb (strictHenselizationBaseChangeToSource B hS f s)
      ((smallEtaleBaseChange f).obj V)
      (strictHenselizationBaseChangeEtaleLift B hS f s V w)
      (by exact pullback.lift_snd _ _ _)).naturality ((smallEtaleAdjunctionAb f).counit.app F)
  have hcounit : (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange f) Ab.{u + 1}
            (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleAdjunctionAb f)
            (𝟙 ((smallEtaleBaseChange f).obj V))).app ((smallEtalePushforwardAb f).obj F) ≫
        ((sheafSections (smallEtaleTopology X) Ab.{u + 1}).obj
            (op ((smallEtaleBaseChange f).obj V))).map
          ((smallEtaleAdjunctionAb f).counit.app F) =
      𝟙 (((smallEtalePushforwardAb f).obj F).obj.obj (op V)) :=
    Stacks.Sites.sectionsPullbackComparison_id_comp_counit (smallEtaleBaseChange f) Ab.{u + 1}
      (smallEtaleTopology S) (smallEtaleTopology X) (smallEtaleAdjunctionAb f) V F
  have step0 : (Scheme.pointSmallEtale s.hom).toPresheafFiber V w
          ((smallEtalePushforwardAb f).obj F).obj ≫
        (pushforwardStalkToStrictHenselizationSectionsAb B hS f s).app F =
      (((Scheme.pointSmallEtale s.hom).toPresheafFiber V w
              ((smallEtalePushforwardAb f).obj F).obj ≫
            (etaleStalkToSectionsAb B S hS s
                (strictHenselizationBaseChangeToStrictHenselization B hS f s)).app
              ((smallEtalePushforwardAb f).obj F)) ≫
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
              Ab.{u + 1}).map
            ((strictHenselizationBaseChangePullbackAbCompIso B hS f s).inv.app
              ((smallEtalePushforwardAb f).obj F))) ≫
        (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).map
          ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).map
            ((smallEtaleAdjunctionAb f).counit.app F)) :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun y => y ≫ (Sheaf.Γ
          (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).map
            ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).map
              ((smallEtaleAdjunctionAb f).counit.app F)))
        (Category.assoc _ _ _).symm)
  exact step0.trans
    ((congrArg (fun y => y ≫ (Sheaf.Γ
            (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).map
              ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).map
                ((smallEtaleAdjunctionAb f).counit.app F)))
        ((congrArg (fun y => y ≫ (Sheaf.Γ
              (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).map
                ((strictHenselizationBaseChangePullbackAbCompIso B hS f s).inv.app
                  ((smallEtalePushforwardAb f).obj F))) hgerm).trans hcomp)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun y => (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange f)
                Ab.{u + 1} (smallEtaleTopology S) (smallEtaleTopology X)
                (smallEtaleAdjunctionAb f)
                (𝟙 ((smallEtaleBaseChange f).obj V))).app
              ((smallEtalePushforwardAb f).obj F) ≫ y) hnat.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun y => y ≫ (smallEtaleSectionsPullbackAb
                  (strictHenselizationBaseChangeToSource B hS f s)
                  ((smallEtaleBaseChange f).obj V)
                  (strictHenselizationBaseChangeEtaleLift B hS f s V w)
                  (by exact pullback.lift_snd _ _ _)).app F) hcounit).trans
              (Category.id_comp _))))))

end Germ

/-! ### The square on abelian sheaves -/

section Square

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- The morphism `id_X × c` carries the canonical morphism into the base change `X ×_S V` of an
étale neighbourhood `(V, w)` of `s` to the canonical morphism for the specialized
neighbourhood. -/
theorem strictHenselizationBaseChangeSpecializationMap_comp_etaleLift (V : S.Etale)
    (w : (Scheme.pointSmallEtale s.hom).fiber.obj V) :
    strictHenselizationBaseChangeSpecializationMap B hS f s t ≫
        strictHenselizationBaseChangeEtaleLift B hS f s V w =
      strictHenselizationBaseChangeEtaleLift B hS f
        (t.map (strictHenselizationToBase B S hS s)) V
        (specializationEtaleNeighborhoodLift B S hS s t V w) := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun y => strictHenselizationBaseChangeSpecializationMap B hS f s t ≫ y)
      (pullback.lift_fst _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun y : strictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s)) ⟶ strictHenselization B S hS s =>
        y ≫ strictHenselizationNeighborhoodLift B S hS s V w)
      (strictHenselizationBaseChangeSpecializationMap_comp_toStrictHenselization
        B hS f s t)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun y : strictHenselization B S hS
          (t.map (strictHenselizationToBase B S hS s)) ⟶ V.left =>
        strictHenselizationBaseChangeToStrictHenselization B hS f
          (t.map (strictHenselizationToBase B S hS s)) ≫ y)
      (specializationMorphism_comp_neighborhoodLift B S hS s t V w)).trans ?_
    exact (pullback.lift_fst _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun y => strictHenselizationBaseChangeSpecializationMap B hS f s t ≫ y)
      (pullback.lift_snd _ _ _)).trans ?_
    exact (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t).trans
      (pullback.lift_snd _ _ _).symm

/-- **The square on abelian sheaves.** The map `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`
of Stacks 0GIX at `s`, followed by restriction of sections along `id_X × c`, is the
specialization map `sp : (f_*F)_s ⟶ (f_*F)_{t ≫ p}` followed by the same map at `t ≫ p`.

Both sides are maps out of the stalk at `s` of the direct image, so it suffices to compare them
on the germ of a section over an étale neighbourhood `(V, w)` of `s`; there both are restriction
along `X ×_S Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ X ×_S V` of the corresponding section of `F` over
`X ×_S V`, the two morphisms agreeing because `c` carries the canonical morphism from the strict
henselization into `V` to the one for the specialized neighbourhood. -/
@[stacks 0GJ8 "the square for an abelian sheaf `F`, in place of an object `K` of `D⁺(X_étale)`: \
the vertical identifications are those of Stacks 0GIX rather than their derived counterparts"]
theorem pushforwardStalkToStrictHenselizationSectionsAb_comp_sectionsRestrictionAb :
    pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
        smallEtaleSectionsRestrictionAb (strictHenselizationBaseChangeToSource B hS f s)
          (strictHenselizationBaseChangeSpecializationMap B hS f s t)
          (strictHenselizationBaseChangeToSource B hS f
            (t.map (strictHenselizationToBase B S hS s)))
          (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t) =
      Functor.whiskerLeft (smallEtalePushforwardAb f)
          (smallEtaleSpecializationStalkAb B S hS s t) ≫
        pushforwardStalkToStrictHenselizationSectionsAb B hS f
          (t.map (strictHenselizationToBase B S hS s)) := by
  ext F : 2
  refine smallEtaleStalkAb_hom_ext s.hom ((smallEtalePushforwardAb f).obj F) fun V w => ?_
  refine ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun y => y ≫ (smallEtaleSectionsRestrictionAb
            (strictHenselizationBaseChangeToSource B hS f s)
            (strictHenselizationBaseChangeSpecializationMap B hS f s t)
            (strictHenselizationBaseChangeToSource B hS f
              (t.map (strictHenselizationToBase B S hS s)))
            (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t)).app F)
        (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS f s V w F)).trans
      (congrArg (fun σ => NatTrans.app σ F)
        (smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb
          (strictHenselizationBaseChangeToSource B hS f s)
          ((smallEtaleBaseChange f).obj V)
          (strictHenselizationBaseChangeSpecializationMap B hS f s t)
          (strictHenselizationBaseChangeToSource B hS f
            (t.map (strictHenselizationToBase B S hS s)))
          (strictHenselizationBaseChangeEtaleLift B hS f s V w)
          (by exact pullback.lift_snd _ _ _)
          (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t)
          (strictHenselizationBaseChangeEtaleLift B hS f
            (t.map (strictHenselizationToBase B S hS s)) V
            (specializationEtaleNeighborhoodLift B S hS s t V w))
          (by exact pullback.lift_snd _ _ _)
          (strictHenselizationBaseChangeSpecializationMap_comp_etaleLift
            B hS f s t V w))))).trans
    (((Category.assoc _ _ _).symm.trans
      ((congrArg (fun y => y ≫ (pushforwardStalkToStrictHenselizationSectionsAb B hS f
              (t.map (strictHenselizationToBase B S hS s))).app F)
          (smallEtaleSpecializationStalkAb_toPresheafFiber B S hS s t
            ((smallEtalePushforwardAb f).obj F) V w)).trans
        (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS f
          (t.map (strictHenselizationToBase B S hS s)) V
          (specializationEtaleNeighborhoodLift B S hS s t V w) F))).symm)

end Square

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-! ### The composition isomorphism for derived inverse image -/

section DerivedComp

attribute [local instance] HasDerivedCategory.standard

variable {Z T T' : Scheme.{u}} {b : T ⟶ Z} {a : T' ⟶ T} {c : T' ⟶ Z}
  (χ : smallEtalePullbackAb b ⋙ smallEtalePullbackAb a ≅ smallEtalePullbackAb c)

/-- The identification of the composite of two derived inverse images with a third, induced by an
identification of the corresponding degreewise inverse images, for instance the composition
isomorphism `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso`.

This is the lift of the degreewise identification through `DerivedCategory.Qh`, which is what
makes its effect on the image of a complex computable:
`Stacks.EtaleCohomology.smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app`. The general
`CategoryTheory.Functor.mapDerivedCategoryCompIso` is instead a lift through
`DerivedCategory.Q`, and has no such characterization.

Not to be confused with `Stacks.EtaleCohomology.smallEtaleDerivedPullbackCompIso` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting`, which is a
different statement about a different functor: that one compares
`(smallEtalePullbackAb f' ⋙ smallEtalePullbackAb f'').rightDerivedFunctorPlus` with the
composite of the two right derived functors, whereas this one identifies a composite of
`smallEtaleDerivedPullbackAb`s, whence the `Ab` in the name. -/
def smallEtaleDerivedPullbackAbCompIsoQhLift :
    smallEtaleDerivedPullbackAb b ⋙ smallEtaleDerivedPullbackAb a ≅
      smallEtaleDerivedPullbackAb c :=
  Localization.liftNatIso DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))
    (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ⋙
      smallEtaleDerivedPullbackAb a)
    ((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (smallEtaleDerivedPullbackAb b ⋙ smallEtaleDerivedPullbackAb a)
    (smallEtaleDerivedPullbackAb c)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ))
        (smallEtalePullbackAb a).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso χ (.up ℤ))
        DerivedCategory.Qh)

/-- On the image of a complex, the identification of the composite of two derived inverse images
is the degreewise identification, read through the identifications of the degreewise actions of
the three inverse-image functors with their actions on derived categories. -/
theorem smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedPullbackAbCompIsoQhLift χ).hom.app (DerivedCategory.Qh.obj J) =
      (smallEtaleDerivedPullbackAb a).map
          ((smallEtalePullbackAb b).mapDerivedCategoryFactorsh.hom.app J) ≫
        (smallEtalePullbackAb a).mapDerivedCategoryFactorsh.hom.app
            (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J) ≫
          DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso χ (.up ℤ)).hom.app J) ≫
            (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J := by
  simp [smallEtaleDerivedPullbackAbCompIsoQhLift]
  rfl

end DerivedComp

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-! ### The bottom arrow of the square on unbounded derived categories -/

section DerivedBottom

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s))))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s)))) Ab.{u + 1}) (.up ℤ))]

/-- Inverse image along the projection `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`, followed by inverse image
along `id_X × c`, is inverse image along the projection `X ×_S Spec(𝒪^{sh}_{S,t ≫ p}) ⟶ X`: the
composition isomorphism for inverse images, read through the fact that `id_X × c` lies over
`X`. -/
def strictHenselizationBaseChangeSpecializationPullbackAbCompIso :
    smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtalePullbackAb (strictHenselizationBaseChangeSpecializationMap B hS f s t) ≅
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f
        (t.map (strictHenselizationToBase B S hS s))) :=
  smallEtalePullbackAbCompIso (strictHenselizationBaseChangeSpecializationMap B hS f s t)
      (strictHenselizationBaseChangeToSource B hS f s) ≪≫
    eqToIso (congrArg (fun m : strictHenselizationBaseChange B hS f
        (t.map (strictHenselizationToBase B S hS s)) ⟶ X => smallEtalePullbackAb m)
      (strictHenselizationBaseChangeSpecializationMap_comp_toSource B hS f s t))

/-- **The bottom arrow of Stacks 0GJ8.** The canonical map

`RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,t ≫ p}), p⁻¹K)`

for an object `K` of the unbounded derived category of abelian sheaves on the small étale site of
`X`, natural in `K`: pullback by `id_X × c`, after identifying the inverse image along `id_X × c`
of `p⁻¹K` with the inverse image of `K` along the projection to `X` from the second base
change. -/
def strictHenselizationSectionsSpecialization :
    smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) ⟶
      smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f
          (t.map (strictHenselizationToBase B S hS s))) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
          (t.map (strictHenselizationToBase B S hS s))) :=
  Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
      (smallEtaleDerivedGlobalSectionsRestriction
        (strictHenselizationBaseChangeSpecializationMap B hS f s t)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (smallEtaleDerivedPullbackAbCompIsoQhLift
        (strictHenselizationBaseChangeSpecializationPullbackAbCompIso B hS f s t)).hom
      (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f
        (t.map (strictHenselizationToBase B S hS s))))

end DerivedBottom

end AlgebraicGeometry

end
