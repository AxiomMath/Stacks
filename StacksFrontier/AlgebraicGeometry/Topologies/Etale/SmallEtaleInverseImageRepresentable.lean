module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison

/-!
# The inverse image of a representable sheaf on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes and let `V` be an étale `Y`-scheme. The sheaf on the
small étale site of `Y` represented by `V` is carried by the inverse image to the sheaf on the
small étale site of `X` represented by the base change `X ×_Y V`, naturally in `V`.

Representable presheaves are sheaves for the small étale topology, so that topology is
subcanonical and the representable sheaf is `GrothendieckTopology.uliftYoneda`, whose values are
the sets of étale `Y`-morphisms into `V`, lifted into the coefficient universe.

## Main results

* `AlgebraicGeometry.Scheme.subcanonical_smallEtaleTopology`: the small étale topology of a
  scheme is subcanonical.
* `Stacks.EtaleCohomology.smallEtalePullbackRepresentableIso`: the isomorphism for a single
  étale `Y`-scheme, with `Stacks.EtaleCohomology.smallEtalePullbackRepresentableIso_hom_comp`
  its defining property.
* `Stacks.EtaleCohomology.smallEtalePullbackRepresentableNatIso` and
  `Stacks.EtaleCohomology.smallEtalePullbackRepresentableNatIso_app_hom_comp`: the
  isomorphism, natural in the étale `Y`-scheme, and the equation characterizing it.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03O4](https://stacks.math.columbia.edu/tag/03O4)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Scheme

/-- The small étale topology of a scheme is subcanonical: every representable presheaf on the
small étale site is a sheaf. -/
public instance subcanonical_smallEtaleTopology (S : Scheme.{u}) :
    (smallEtaleTopology S).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun V ↦
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (isSheaf_smallEtale_of_isRepresentable S (yoneda.obj V))

end AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Precomposing the direct image with evaluation at an étale `Y`-scheme `V`: the functor
`F ↦ (f_* F)(V)` on sheaves of sets on the small étale site of `X`. -/
public abbrev smallEtaleSectionsAlong (V : Y.Etale) :
    Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)) ⥤ Type (max (u + 1) v) :=
  (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X) ⋙
    (sheafSections (smallEtaleTopology Y) (Type (max (u + 1) v))).obj (op V)

/-- The inverse image of the sheaf represented by `V` corepresents `F ↦ (f_* F)(V)`, through the
inverse-image/direct-image adjunction followed by the Yoneda bijection for sheaves. -/
public def corepSmallEtalePullbackRepresentable (V : Y.Etale) :
    (smallEtaleSectionsAlong.{u, v} f V).CorepresentableBy
      (((smallEtaleBaseChange f).sheafPullback (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).obj
        ((smallEtaleTopology Y).uliftYoneda.{max (u + 1) v}.obj V)) where
  homEquiv := (((smallEtaleBaseChange f).sheafAdjunctionContinuous (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X)).homEquiv _ _).trans
    (smallEtaleTopology Y).uliftYonedaEquiv
  homEquiv_comp g h := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right,
      (smallEtaleTopology Y).uliftYonedaEquiv_comp]
    rfl

/-- The sheaf represented by the base change `X ×_Y V` corepresents `F ↦ (f_* F)(V)`, by the
Yoneda bijection for sheaves. -/
public def corepSmallEtaleRepresentable (V : Y.Etale) :
    (smallEtaleSectionsAlong.{u, v} f V).CorepresentableBy
      ((smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
        ((smallEtaleBaseChange f).obj V)) where
  homEquiv := (smallEtaleTopology X).uliftYonedaEquiv
  homEquiv_comp g h := (smallEtaleTopology X).uliftYonedaEquiv_comp h g

/-- Naturality in `V` of the corepresentability bijection for the inverse image of a
representable: precomposing with the inverse image of `h_g` restricts along `g`. -/
public lemma corepSmallEtalePullbackRepresentable_homEquiv_map {V W : Y.Etale} (g : V ⟶ W)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (h : ((smallEtaleBaseChange f).sheafPullback (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).obj
        ((smallEtaleTopology Y).uliftYoneda.{max (u + 1) v}.obj W) ⟶ F) :
    (corepSmallEtalePullbackRepresentable.{u, v} f V).homEquiv
        (((smallEtaleBaseChange f).sheafPullback (Type (max (u + 1) v))
          (smallEtaleTopology Y) (smallEtaleTopology X)).map
          ((smallEtaleTopology Y).uliftYoneda.map g) ≫ h) =
      (((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).obj F).obj.map g.op
          ((corepSmallEtalePullbackRepresentable.{u, v} f W).homEquiv h) := by
  dsimp only [corepSmallEtalePullbackRepresentable, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact ((smallEtaleTopology Y).uliftYonedaEquiv_naturality _ _).symm

/-- Naturality in `V` of the Yoneda bijection for the representable of the base change. -/
public lemma corepSmallEtaleRepresentable_homEquiv_map {V W : Y.Etale} (g : V ⟶ W)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (h : (smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
        ((smallEtaleBaseChange f).obj W) ⟶ F) :
    (corepSmallEtaleRepresentable.{u, v} f V).homEquiv
        ((smallEtaleTopology X).uliftYoneda.map ((smallEtaleBaseChange f).map g) ≫ h) =
      (((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).obj F).obj.map g.op
          ((corepSmallEtaleRepresentable.{u, v} f W).homEquiv h) :=
  ((smallEtaleTopology X).uliftYonedaEquiv_naturality _ _).symm

/-- For two corepresentations of one functor, precomposing with the isomorphism
`CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso` of their corepresenting objects carries
one bijection to the other. -/
private lemma homEquiv_uniqueUpToIso_hom_comp {C : Type*} [Category C] {F : C ⥤ Type v}
    {A B : C} (e : F.CorepresentableBy A) (e' : F.CorepresentableBy B) {Z : C} (g : B ⟶ Z) :
    e.homEquiv ((e.uniqueUpToIso e').hom ≫ g) = e'.homEquiv g := by
  rw [e.homEquiv_comp, e'.homEquiv_eq g]
  congr 1
  rw [Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage]
  simp [NatIso.ofComponents]

/-- The inverse image of the sheaf represented by an étale `Y`-scheme `V` is the sheaf
represented by the base change `X ×_Y V`. -/
public def smallEtalePullbackRepresentableIso (V : Y.Etale) :
    ((smallEtaleBaseChange f).sheafPullback (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)).obj
        ((smallEtaleTopology Y).uliftYoneda.{max (u + 1) v}.obj V) ≅
      (smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
        ((smallEtaleBaseChange f).obj V) :=
  (corepSmallEtalePullbackRepresentable.{u, v} f V).uniqueUpToIso
    (corepSmallEtaleRepresentable.{u, v} f V)

/-- The defining property of `smallEtalePullbackRepresentableIso`: precomposing with it carries
the corepresentability bijection of the representable of `X ×_Y V` to that of the inverse image
of the representable of `V`. -/
public lemma smallEtalePullbackRepresentableIso_hom_comp (V : Y.Etale)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (g : (smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
      ((smallEtaleBaseChange f).obj V) ⟶ F) :
    (corepSmallEtalePullbackRepresentable.{u, v} f V).homEquiv
        ((smallEtalePullbackRepresentableIso.{u, v} f V).hom ≫ g) =
      (corepSmallEtaleRepresentable.{u, v} f V).homEquiv g :=
  homEquiv_uniqueUpToIso_hom_comp _ _ g

/-- For a morphism of schemes `f : X ⟶ Y`, the inverse image on the small étale sites carries the
sheaf represented by an étale `Y`-scheme `V` to the sheaf represented by the base change
`X ×_Y V`, naturally in `V`: `f⁻¹ h_V ≅ h_{X ×_Y V}` as functors of `V`. -/
@[stacks 03Q1 "pullback_representable"]
public def smallEtalePullbackRepresentableNatIso :
    (smallEtaleTopology Y).uliftYoneda.{max (u + 1) v} ⋙
        (smallEtaleBaseChange f).sheafPullback (Type (max (u + 1) v))
          (smallEtaleTopology Y) (smallEtaleTopology X) ≅
      smallEtaleBaseChange f ⋙ (smallEtaleTopology X).uliftYoneda.{max (u + 1) v} :=
  NatIso.ofComponents (smallEtalePullbackRepresentableIso.{u, v} f) (by
    intro V W g
    apply (corepSmallEtalePullbackRepresentable.{u, v} f V).homEquiv.injective
    have hL := corepSmallEtalePullbackRepresentable_homEquiv_map.{u, v} f g _
      (smallEtalePullbackRepresentableIso.{u, v} f W).hom
    have hI := smallEtalePullbackRepresentableIso_hom_comp.{u, v} f W _ (𝟙 _)
    rw [Category.comp_id] at hI
    have hY := corepSmallEtaleRepresentable_homEquiv_map.{u, v} f g
      ((smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
        ((smallEtaleBaseChange f).obj W)) (𝟙 _)
    rw [Category.comp_id] at hY
    dsimp only [Functor.comp_map]
    rw [hL, hI, ← hY]
    exact (smallEtalePullbackRepresentableIso_hom_comp.{u, v} f V _ _).symm)

/-- Under the inverse-image/direct-image adjunction and the Yoneda bijections for sheaves,
precomposition with the component of `smallEtalePullbackRepresentableNatIso` at `V` is the
identity on sections over `X ×_Y V`. -/
@[stacks 03Q1 "pullback_representable"]
public lemma smallEtalePullbackRepresentableNatIso_app_hom_comp (V : Y.Etale)
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (g : (smallEtaleTopology X).uliftYoneda.{max (u + 1) v}.obj
      ((smallEtaleBaseChange f).obj V) ⟶ F) :
    (smallEtaleTopology Y).uliftYonedaEquiv
        ((((smallEtaleBaseChange f).sheafAdjunctionContinuous (Type (max (u + 1) v))
          (smallEtaleTopology Y) (smallEtaleTopology X)).homEquiv _ _)
            (((smallEtalePullbackRepresentableNatIso.{u, v} f).app V).hom ≫ g)) =
      (smallEtaleTopology X).uliftYonedaEquiv g :=
  smallEtalePullbackRepresentableIso_hom_comp.{u, v} f V F g

end Stacks.EtaleCohomology

end
