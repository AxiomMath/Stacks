module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.RelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.RelocalizationTriangle

/-!
# The direct image of a relocalization, as restriction along a fibre product

Let `(C, O)` be a ringed site whose underlying category has fibre products, and let `a : A ⟶ D`
be a morphism of `C`. The relocalization morphism of ringed topoi of Stacks 04IY,
`AlgebraicGeometry.RingedSite.relocalizationRingedToposHom`, has for its underlying morphism of
topoi the one attached to the *cocontinuous* functor `Over.map a : C/A ⥤ C/D`, so its direct
image is a chosen right adjoint of restriction along `Over.map a`. Restriction along
`Over.pullback a : C/D ⥤ C/A` is another such right adjoint, by Stacks 09W9, so the two are
canonically isomorphic; this file records that comparison and computes what it does to the
structure map of the relocalization.

## Main definitions

* `AlgebraicGeometry.RingedSite.relocalizationDirectImageIso`: the comparison of the direct
  image of the relocalization along `a` with restriction along `Over.pullback a`.

## Main results

* `AlgebraicGeometry.RingedSite.relocalizationDirectImageIso_fSharp_app`: on sections over an
  object `T/D` of the localization at `D`, the structure map of the relocalization followed by
  the comparison is restriction of regular functions along the projection `T ×_D A ⟶ T`.
* `AlgebraicGeometry.RingedSite.forgetFSharp_comp_ringedToposHom` and
  `AlgebraicGeometry.RingedSite.forgetFSharp_comp_ringedToposHom_comp`: the structure map, on
  underlying sheaves of sets, of a composite of morphisms of ringed topoi coming from
  morphisms of ringed *sites*, spelled out in terms of the structure maps of the latter.

## Implementation notes

Both sides are right adjoints of one and the same functor, namely restriction along
`Over.map a`, so the comparison is `CategoryTheory.Adjunction.rightAdjointUniq` of the
cocontinuous-pushforward adjunction of `Over.map a` and of
`CategoryTheory.Adjunction.sheafPushforwardContinuous` applied to
`CategoryTheory.Over.mapPullbackAdj a`.

That presentation is what makes the computation on sections short. The structure map of the
relocalization is, on underlying sheaves of sets, the unit of the first adjunction
(`AlgebraicGeometry.RingedSite.forgetRing_relocalizationRingedToposHom_fSharp`), uniqueness of
right adjoints carries a unit to a unit
(`CategoryTheory.Adjunction.unit_rightAdjointUniq_hom_app`), and the unit of the second
adjunction is restriction along the counit of `Over.mapPullbackAdj a`, which is the fibre-product
projection.

The equalities below are chained with `Eq.trans` and `congrArg` rather than with `rw`: the three
spellings of the restricted structure sheaf that the adjunctions produce agree only up to
unfolding `CategoryTheory.Over.map`, so the motives that `rw` would build are not type-correct
at reducible transparency.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 09W9](https://stacks.math.columbia.edu/tag/09W9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u}) [HasPullbacks Z.C] {A D : Z.C} (a : A ⟶ D)

/-- The direct image of the relocalization of `(C, O)` along `a : A ⟶ D` is restriction along
`Over.pullback a`: both are right adjoint to restriction along `Over.map a`. -/
noncomputable def relocalizationDirectImageIso :
    (Z.relocalizationRingedToposHom a).toToposHom.pushforward ≅
      (Over.pullback a).sheafPushforwardContinuous (Type u) (Z.J.over D) (Z.J.over A) :=
  Adjunction.rightAdjointUniq
    ((Over.map a).sheafAdjunctionCocontinuous (Type u) (Z.J.over A) (Z.J.over D))
    ((Over.mapPullbackAdj a).sheafPushforwardContinuous (Z.J.over A) (Z.J.over D)
      (E := Type u))

/-- The structure map of the relocalization along `a : A ⟶ D`, followed by the comparison of
its direct image with restriction along `Over.pullback a`, is on sections over an object `T/D`
the restriction map of `O` along the fibre-product projection `T ×_D A ⟶ T`. -/
theorem relocalizationDirectImageIso_fSharp_app (T : (Over D)ᵒᵖ) :
    ((AlgebraicGeometry.RingedToposHom.forgetFSharp (Z.relocalizationRingedToposHom a) ≫
        (Z.relocalizationDirectImageIso a).hom.app
          ((ringedTopos (Z.over A)).forgetRing.obj (Z.over A).O)).hom.app T) =
      (forget CommRingCat.{u}).map (Z.O.obj.map (pullback.fst T.unop.hom a).op) := by
  have hstep := Adjunction.unit_rightAdjointUniq_hom_app
    ((Over.map a).sheafAdjunctionCocontinuous (Type u) (Z.J.over A) (Z.J.over D))
    ((Over.mapPullbackAdj a).sheafPushforwardContinuous (Z.J.over A) (Z.J.over D)
      (E := Type u))
    ((ringedTopos (Z.over D)).forgetRing.obj (Z.over D).O)
  have h2 := Adjunction.sheafPushforwardContinuous_unit_app_hom_app (Over.mapPullbackAdj a)
    (Z.J.over A) (Z.J.over D) ((ringedTopos (Z.over D)).forgetRing.obj (Z.over D).O) T
  have hu : AlgebraicGeometry.RingedToposHom.forgetFSharp
      (Z.relocalizationRingedToposHom a) =
      (Z.overMapMorphismOfTopoi a).adj.unit.app
        ((ringedTopos (Z.over D)).forgetRing.obj (Z.over D).O) :=
    Z.forgetRing_relocalizationRingedToposHom_fSharp a
  refine ((congrArg (fun z => (z ≫ (Z.relocalizationDirectImageIso a).hom.app
      ((ringedTopos (Z.over A)).forgetRing.obj (Z.over A).O)).hom.app T) hu).trans
    (((congrArg (fun z => z.hom.app T) hstep).trans h2).trans ?_))
  simp only [Over.mapPullbackAdj_counit_app]
  rfl

/-! ### Structure maps of composites

A 2-morphism between two composites of morphisms of ringed topoi has to compare their structure
maps, and the composites that occur in Stacks 04J1 are built from morphisms of ringed *sites*.
The two lemmas below rewrite the structure map of such a composite, on underlying sheaves of
sets, into the structure maps of the morphisms of ringed sites it is built from. They are stated
for abstract ringed sites on purpose: performing the same rewriting on an instantiated goal
re-elaborates the sites and their structure sheaves at every step. -/

variable {A₁ A₂ A₃ A₄ : RingedSite.{u, u, u}}

/-- The structure map of the composite of a morphism of ringed topoi coming from a morphism of
ringed sites with an arbitrary morphism of ringed topoi, on underlying sheaves of sets. -/
private theorem forgetFSharp_comp_ringedToposHom_left (α : RingedSite.Hom A₂ A₄)
    (ε : AlgebraicGeometry.RingedToposHom (ringedTopos A₁) (ringedTopos A₂)) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos A₁) (Y := ringedTopos A₂)
          (Z := ringedTopos A₄) α.ringedToposHom ε) =
      (sheafCompose A₄.J (forget CommRingCat.{u})).map α.fsharp ≫
        α.toposHom.pushforward.map (AlgebraicGeometry.RingedToposHom.forgetFSharp ε) :=
  (AlgebraicGeometry.RingedToposHom.forgetFSharp_comp α.ringedToposHom ε).trans
    (congrArg (fun z => z ≫ α.toposHom.pushforward.map
      (AlgebraicGeometry.RingedToposHom.forgetFSharp ε)) (Hom.forgetFSharp_ringedToposHom α))

/-- The structure map of the composite of two morphisms of ringed topoi coming from morphisms
of ringed sites, on underlying sheaves of sets. -/
theorem forgetFSharp_comp_ringedToposHom (α : RingedSite.Hom A₂ A₄) (β : RingedSite.Hom A₁ A₂) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos A₁) (Y := ringedTopos A₂)
          (Z := ringedTopos A₄) α.ringedToposHom β.ringedToposHom) =
      (sheafCompose A₄.J (forget CommRingCat.{u})).map α.fsharp ≫
        α.toposHom.pushforward.map
          ((sheafCompose A₂.J (forget CommRingCat.{u})).map β.fsharp) :=
  (forgetFSharp_comp_ringedToposHom_left α β.ringedToposHom).trans
    (congrArg (fun z => (sheafCompose A₄.J (forget CommRingCat.{u})).map α.fsharp ≫
      α.toposHom.pushforward.map z) (Hom.forgetFSharp_ringedToposHom β))

/-- The structure map of the composite of a morphism of ringed topoi coming from a morphism of
ringed sites with a composite of such a morphism and an arbitrary morphism of ringed topoi, on
underlying sheaves of sets. This is the shape of the two composites compared in Stacks 04J1. -/
theorem forgetFSharp_comp_ringedToposHom_comp (α : RingedSite.Hom A₃ A₄)
    (β : RingedSite.Hom A₂ A₃)
    (δ : AlgebraicGeometry.RingedToposHom (ringedTopos A₁) (ringedTopos A₂)) :
    AlgebraicGeometry.RingedToposHom.forgetFSharp
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos A₁) (Y := ringedTopos A₃)
          (Z := ringedTopos A₄) α.ringedToposHom
          (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos A₁) (Y := ringedTopos A₂)
            (Z := ringedTopos A₃) β.ringedToposHom δ)) =
      (sheafCompose A₄.J (forget CommRingCat.{u})).map α.fsharp ≫
        α.toposHom.pushforward.map
          ((sheafCompose A₃.J (forget CommRingCat.{u})).map β.fsharp ≫
            β.toposHom.pushforward.map
              (AlgebraicGeometry.RingedToposHom.forgetFSharp δ)) :=
  (forgetFSharp_comp_ringedToposHom_left α _).trans
    (congrArg (fun z => (sheafCompose A₄.J (forget CommRingCat.{u})).map α.fsharp ≫
      α.toposHom.pushforward.map z) (forgetFSharp_comp_ringedToposHom_left β δ))

end AlgebraicGeometry.RingedSite

end
