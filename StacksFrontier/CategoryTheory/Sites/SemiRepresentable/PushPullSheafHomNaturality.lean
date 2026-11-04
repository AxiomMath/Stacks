module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekObjectNaturality
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.RelocalizationRestrictionComponents

/-!
# Stacks 0D86 is natural in the semi-representable object

Let `(C, J)` be a small site and `f : M ⟶ N` a morphism of semi-representable objects of `C`.
`CategoryTheory.SemiRepresentable.pushPullSheafHomIso` identifies push-pull along the
componentwise localization functor `j_M` with the internal hom `SheafHom(F(M)^#, -)`, which is
Stacks 0D86 read through the product description of sheaves on `C/M`. On the left a morphism of
semi-representable objects induces
`CategoryTheory.SemiRepresentable.pushPullRestrictionTransition`, the canonical transition
`j_{N,*}j_N^{-1} ⟶ j_{M,*}j_M^{-1}`, and on the right it induces
`CategoryTheory.SheafHomAdj.sheafHomContraMap` of `F(f)^#`. This file is the square saying that
the two correspond.

The square splits at the two factors of `pushPullSheafHomIso`. The factor
`CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom` — Stacks 0D86
proper, the comparison of the product of the push-pulls of the components with the product of the
internal homs — is already known to be natural, which is
`CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom_naturality`. The
other factor is `CategoryTheory.SemiRepresentable.pushPullProductIso`, the product description of
push-pull along `j_M`, and its naturality is what this file proves.

Both sides of that second square are maps into a product, and their `i`-th projections land in
`j_{M_i,*}j_{M_i}^{-1}`, so the localization adjunction at `M_i` turns the square into an
equation of adjuncts, one component at a time. Each adjunct is a mate. On the left it is the mate
of the transition, `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition_mate`,
restricted to the component `i`; on the right it is the mate of
`CategoryTheory.SemiRepresentable.pushPullContraMap`, which is a mate at all because Stacks 03EE
is natural in the object — that is
`CategoryTheory.SemiRepresentable.pushPullContraMap_eq_restrictionTransition`. The two agree
because restriction along `r_f` is componentwise restriction along `Over.map (f.φ i)`
(`CategoryTheory.SemiRepresentable.componentOverMap_sheafPushforwardContinuous_comp_restrictSheaf`)
and the front face of the cube of Stacks 0D8E is componentwise its one-object case
(`CategoryTheory.SemiRepresentable.restrictSheaf_map_relocalizationForgetPushforwardIso_hom`).

## Main results

* `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition_comp_pushPullProductIso`: **the
  product description of push-pull is natural in the semi-representable object**, the second
  factor of the square.
* `CategoryTheory.SemiRepresentable.pushPullSheafHomIso_naturality`: **Stacks 0D86 is natural in
  the semi-representable object.**

## Implementation notes

The two `Iso.trans` factors of `pushPullSheafHomIso` are separated by `show`, not by
`CategoryTheory.Iso.trans_hom`: `Iso.trans` is `implicit_reducible`, so `(α ≪≫ β).hom` is already
in `simp`-normal form and `Iso.trans_hom` never fires on it.

`CategoryTheory.SemiRepresentable.productPushPullFunctor` is semireducible, so
`(productPushPullFunctor J M).obj X` and the product `∏ᶜ` it unfolds to are interchangeable only
at default transparency: a goal composing a component of `pushPullProductIso` with
`CategoryTheory.Limits.Pi.π` is not type-correct at reducible transparency, and `rw` and
`simp only [Category.assoc]` refuse to act on it. The projection is therefore confined to two
places. In `pushPullRestrictionTransition_comp_pushPullProductIso_app_π` every step that mentions
it is term mode, where elaboration is at default transparency; and the two lemmas that do the
rewriting, `pushPullRestrictionTransition_comp_adjunct` and `pushPullContraMap_comp_adjunct`,
take the map into the `i`-th factor as a free variable, so no projection occurs in their goals
and `rw` works there.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 03EE](https://stacks.math.columbia.edu/tag/03EE)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open Stacks.CategoryTheory

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

section Components

variable {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

/-- **The mate of the push-pull restriction transition, restricted to a component.** Reading the
mate of `CategoryTheory.SemiRepresentable.pushPullRestrictionTransition` through the product
description of sheaves on `C/M` gives, at the component indexed by `i`, the one-object
relocalization comparison of `f.φ i`, the restriction along `Over.map (f.φ i)` of the `f(i)`-th
component of the push-pull counit of `j_N`, and the comparison again.

The middle factor is an equality of functors
(`componentOverMap_sheafPushforwardContinuous_comp_restrictSheaf`), and the two outer ones are
`restrictSheaf_map_relocalizationForgetPushforwardIso_inv` and `..._hom`. -/
theorem restrictSheaf_map_pushPullRestrictionTransition_mate (X : Sheaf J (Type u)) (i : M.I) :
    (restrictSheaf J M (Type u)).map
        (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).map
            ((pushPullRestrictionTransition J f (componentwiseTopology J M) rfl
              (componentwiseTopology J N) rfl).app X) ≫
          ((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
              (componentwiseTopology J M) J).counit.app
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) i =
      (overMapPullbackIso J (f.φ i)).inv.app
          (((componentOverForget N).sheafPushforwardCocontinuous (Type u)
              (componentwiseTopology J N) J).obj
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X)) ≫
        ((Over.map (f.φ i)).sheafPushforwardContinuous (Type u) (J.over (M.obj i))
              (J.over (N.obj (f.f i)))).map
            ((restrictSheaf J N (Type u)).map
              (((componentOverForget N).sheafAdjunctionCocontinuous (Type u)
                  (componentwiseTopology J N) J).counit.app
                (((componentOverForget N).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J N) J).obj X)) (f.f i)) ≫
          (overMapPullbackIso J (f.φ i)).hom.app X := by
  rw [pushPullRestrictionTransition_mate, Functor.map_comp, Functor.map_comp, Pi.comp_apply,
    Pi.comp_apply, restrictSheaf_map_relocalizationForgetPushforwardIso_inv,
    restrictSheaf_map_relocalizationForgetPushforwardIso_hom]
  rfl

/-- **The mate of restriction along `g : U ⟶ V` on push-pull.** The adjunct of
`CategoryTheory.SemiRepresentable.pushPullContraMap` under the localization adjunction at `U` is
the counit of the one at `V`, restricted along `Over.map g` and conjugated by the one-object
relocalization comparison.

`pushPullContraMap` is defined as a conjugate of `h_g^# × -`; it is a mate of the relocalization
triangle because Stacks 03EE is natural in the object, which is
`pushPullContraMap_eq_restrictionTransition`. -/
theorem pushPullContraMap_mate (X : Sheaf J (Type u)) (i : M.I) :
    (localizationPullback (M.obj i) J).map ((pushPullContraMap J (f.φ i)).app X) ≫
        (localizationAdjunction J (M.obj i)).counit.app
          ((localizationPullback (M.obj i) J).obj X) =
      (overMapPullbackIso J (f.φ i)).inv.app
          ((localizationPushforward (N.obj (f.f i)) J).obj
            ((localizationPullback (N.obj (f.f i)) J).obj X)) ≫
        ((Over.map (f.φ i)).sheafPushforwardContinuous (Type u) (J.over (M.obj i))
              (J.over (N.obj (f.f i)))).map
            ((localizationAdjunction J (N.obj (f.f i))).counit.app
              ((localizationPullback (N.obj (f.f i)) J).obj X)) ≫
          (overMapPullbackIso J (f.φ i)).hom.app X := by
  rw [pushPullContraMap_eq_restrictionTransition]
  exact restrictionTransition_mate _ _ _ _ X

/-- **The left-hand side of the square, as an adjunct.** The adjunct at `M_i` of the push-pull
restriction transition followed by any map `d` whose own adjunct is the `i`-th component of the
push-pull counit of `j_M`.

`d` is a free variable precisely so that the goal contains no product projection; see the
implementation notes. At the point of use it is `pushPullProductIso` followed by the projection
onto the `i`-th factor. -/
theorem pushPullRestrictionTransition_comp_adjunct (X : Sheaf J (Type u)) (i : M.I)
    (d : ((componentOverForget M).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) J ⋙
          (componentOverForget M).sheafPushforwardCocontinuous (Type u)
            (componentwiseTopology J M) J).obj X ⟶
        (localizationPushforward (M.obj i) J).obj ((localizationPullback (M.obj i) J).obj X))
    (hd : (localizationPullback (M.obj i) J).map d ≫
          (localizationAdjunction J (M.obj i)).counit.app
            ((localizationPullback (M.obj i) J).obj X) =
        (restrictSheaf J M (Type u)).map
          (((componentOverForget M).sheafAdjunctionCocontinuous (Type u)
              (componentwiseTopology J M) J).counit.app
            (((componentOverForget M).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) J).obj X)) i) :
    (localizationPullback (M.obj i) J).map
          ((pushPullRestrictionTransition J f (componentwiseTopology J M) rfl
            (componentwiseTopology J N) rfl).app X ≫ d) ≫
        (localizationAdjunction J (M.obj i)).counit.app
          ((localizationPullback (M.obj i) J).obj X) =
      (overMapPullbackIso J (f.φ i)).inv.app
          (((componentOverForget N).sheafPushforwardCocontinuous (Type u)
              (componentwiseTopology J N) J).obj
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X)) ≫
        ((Over.map (f.φ i)).sheafPushforwardContinuous (Type u) (J.over (M.obj i))
              (J.over (N.obj (f.f i)))).map
            ((restrictSheaf J N (Type u)).map
              (((componentOverForget N).sheafAdjunctionCocontinuous (Type u)
                  (componentwiseTopology J N) J).counit.app
                (((componentOverForget N).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J N) J).obj X)) (f.f i)) ≫
          (overMapPullbackIso J (f.φ i)).hom.app X := by
  rw [Functor.map_comp, Category.assoc, hd,
    ← restrictSheaf_map_pushPullRestrictionTransition_mate J f X i, Functor.map_comp]
  rfl

/-- **The right-hand side of the square, as an adjunct.** The adjunct at `M_i` of any map `c`
whose own adjunct at `N_{f(i)}` is the `f(i)`-th component of the push-pull counit of `j_N`,
followed by restriction along `f.φ i`.

Like `pushPullRestrictionTransition_comp_adjunct`, `c` is free so that no product projection
occurs; at the point of use it is `pushPullProductIso` at `N` followed by the projection onto the
`f(i)`-th factor. The proof is `pushPullContraMap_mate` and the naturality of the one-object
relocalization comparison at `c`. -/
theorem pushPullContraMap_comp_adjunct (X : Sheaf J (Type u)) (i : M.I)
    (c : ((componentOverForget N).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J N) J ⋙
          (componentOverForget N).sheafPushforwardCocontinuous (Type u)
            (componentwiseTopology J N) J).obj X ⟶
        (localizationPushforward (N.obj (f.f i)) J).obj
          ((localizationPullback (N.obj (f.f i)) J).obj X))
    (hc : (localizationPullback (N.obj (f.f i)) J).map c ≫
          (localizationAdjunction J (N.obj (f.f i))).counit.app
            ((localizationPullback (N.obj (f.f i)) J).obj X) =
        (restrictSheaf J N (Type u)).map
          (((componentOverForget N).sheafAdjunctionCocontinuous (Type u)
              (componentwiseTopology J N) J).counit.app
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X)) (f.f i)) :
    (localizationPullback (M.obj i) J).map (c ≫ (pushPullContraMap J (f.φ i)).app X) ≫
        (localizationAdjunction J (M.obj i)).counit.app
          ((localizationPullback (M.obj i) J).obj X) =
      (overMapPullbackIso J (f.φ i)).inv.app
          (((componentOverForget N).sheafPushforwardCocontinuous (Type u)
              (componentwiseTopology J N) J).obj
            (((componentOverForget N).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J N) J).obj X)) ≫
        ((Over.map (f.φ i)).sheafPushforwardContinuous (Type u) (J.over (M.obj i))
              (J.over (N.obj (f.f i)))).map
            ((restrictSheaf J N (Type u)).map
              (((componentOverForget N).sheafAdjunctionCocontinuous (Type u)
                  (componentwiseTopology J N) J).counit.app
                (((componentOverForget N).sheafPushforwardContinuous (Type u)
                  (componentwiseTopology J N) J).obj X)) (f.f i)) ≫
          (overMapPullbackIso J (f.φ i)).hom.app X := by
  rw [Functor.map_comp, Category.assoc, pushPullContraMap_mate, NatTrans.naturality_assoc,
    Functor.comp_map,
    ← Category.assoc (((Over.map (f.φ i)).sheafPushforwardContinuous (Type u) (J.over (M.obj i))
      (J.over (N.obj (f.f i)))).map ((localizationPullback (N.obj (f.f i)) J).map c)),
    ← Functor.map_comp, hc]
  rfl

/-- **The naturality square of the product description of push-pull, at one component.** The
transition `j_{N,*}j_N^{-1} ⟶ j_{M,*}j_M^{-1}` followed by the product description at `M` and the
projection onto the `i`-th factor is the product description at `N`, the projection onto the
`f(i)`-th factor, and restriction along `f.φ i`.

Both sides are maps into `j_{M_i,*}j_{M_i}^{-1}`, so it suffices to compare their adjuncts under
the localization adjunction at `M_i`, which is what `pushPullRestrictionTransition_comp_adjunct`
and `pushPullContraMap_comp_adjunct` compute; the hypotheses those two need are
`pushPullProductIso_mate_π` at `M` and at `N`. -/
theorem pushPullRestrictionTransition_comp_pushPullProductIso_app_π (X : Sheaf J (Type u))
    (i : M.I) :
    (pushPullRestrictionTransition J f (componentwiseTopology J M) rfl
            (componentwiseTopology J N) rfl ≫
          (pushPullProductIso J M (componentwiseTopology J M) rfl).hom).app X ≫
        Pi.π (fun j : M.I => (localizationPullback (M.obj j) J ⋙
          localizationPushforward (M.obj j) J).obj X) i =
      ((pushPullProductIso J N (componentwiseTopology J N) rfl).hom ≫
          piPushPullMap J f).app X ≫
        Pi.π (fun j : M.I => (localizationPullback (M.obj j) J ⋙
          localizationPushforward (M.obj j) J).obj X) i := by
  have hm := fun (P : FormalCoproduct.{u} C) (k : P.I) =>
    ((localizationAdjunction J (P.obj k)).homEquiv_counit _ _ _).symm.trans
      (pushPullProductIso_mate_π J P X k)
  have hassoc :
      ((pushPullProductIso J N (componentwiseTopology J N) rfl).hom.app X ≫
            (piPushPullMap J f).app X) ≫
          Pi.π (fun j : M.I => (localizationPullback (M.obj j) J ⋙
            localizationPushforward (M.obj j) J).obj X) i =
        ((pushPullProductIso J N (componentwiseTopology J N) rfl).hom.app X ≫
            Pi.π (fun j : N.I => (localizationPullback (N.obj j) J ⋙
              localizationPushforward (N.obj j) J).obj X) (f.f i)) ≫
          (pushPullContraMap J (f.φ i)).app X :=
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (piPushPullMap_app_π J f X i)).trans (Category.assoc _ _ _).symm
  refine ((localizationAdjunction J (M.obj i)).homEquiv
    (((componentOverForget N).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J N) J ⋙
        (componentOverForget N).sheafPushforwardCocontinuous (Type u)
          (componentwiseTopology J N) J).obj X)
    ((localizationPullback (M.obj i) J).obj X)).symm.injective ?_
  refine ((localizationAdjunction J (M.obj i)).homEquiv_counit _ _ _).trans ?_
  refine Eq.trans ?_ ((localizationAdjunction J (M.obj i)).homEquiv_counit _ _ _).symm
  erw [Category.assoc, pushPullRestrictionTransition_comp_adjunct J f X i _ (hm M i), hassoc,
    pushPullContraMap_comp_adjunct J f X i _ (hm N (f.f i))]

end Components

variable {M N : FormalCoproduct.{u} C} (f : M ⟶ N)
  (Jm : GrothendieckTopology (ComponentOver M)) (hJm : Jm = componentwiseTopology J M)
  (Jn : GrothendieckTopology (ComponentOver N)) (hJn : Jn = componentwiseTopology J N)
  [(componentOverForget M).IsContinuous Jm J] [(componentOverForget M).IsCocontinuous Jm J]
  [(componentOverForget N).IsContinuous Jn J] [(componentOverForget N).IsCocontinuous Jn J]
  [(componentOverMap f).IsContinuous Jm Jn] [(componentOverMap f).IsCocontinuous Jm Jn]

/-- **The product description of push-pull is natural in the semi-representable object.** For a
morphism `f : M ⟶ N` the square

```
j_{N,*} j_N^{-1} ----≅----> ∏ᵢ j_{N_i,*} j_{N_i}^{-1}
       |                              |
pushPullRestrictionTransition f    piPushPullMap f
       v                              v
j_{M,*} j_M^{-1} ----≅----> ∏ᵢ j_{M_i,*} j_{M_i}^{-1}
```

commutes, the two horizontal isomorphisms being
`CategoryTheory.SemiRepresentable.pushPullProductIso`.

A map into a product is its family of projections, and the `i`-th projection of each side is
`pushPullRestrictionTransition_comp_pushPullProductIso_app_π`. -/
theorem pushPullRestrictionTransition_comp_pushPullProductIso :
    pushPullRestrictionTransition J f Jm hJm Jn hJn ≫ (pushPullProductIso J M Jm hJm).hom =
      (pushPullProductIso J N Jn hJn).hom ≫ piPushPullMap J f := by
  subst hJm
  subst hJn
  exact NatTrans.ext (funext fun X => Limits.Pi.hom_ext _ _ (fun i =>
    pushPullRestrictionTransition_comp_pushPullProductIso_app_π J f X i))

/-- **Stacks 0D86 is natural in the semi-representable object.** For a morphism `f : M ⟶ N` of
semi-representable objects the square

```
j_{N,*} j_N^{-1} ----≅----> SheafHom(F(N)^#, -)
       |                            |
pushPullRestrictionTransition f   SheafHom(F(f)^#, -)
       v                            v
j_{M,*} j_M^{-1} ----≅----> SheafHom(F(M)^#, -)
```

commutes, the two horizontal isomorphisms being
`CategoryTheory.SemiRepresentable.pushPullSheafHomIso`.

The two factors of `pushPullSheafHomIso` contribute the two halves of the proof:
`pushPullRestrictionTransition_comp_pushPullProductIso` for the product description of push-pull,
and `localizationPushforwardPullbackNatIsoSheafHom_naturality` for Stacks 0D86 proper. -/
theorem pushPullSheafHomIso_naturality :
    pushPullRestrictionTransition J f Jm hJm Jn hJn ≫ (pushPullSheafHomIso J M Jm hJm).hom =
      (pushPullSheafHomIso J N Jn hJn).hom ≫
        SheafHomAdj.sheafHomContraMap (totSheafify J f) := by
  show pushPullRestrictionTransition J f Jm hJm Jn hJn ≫
      (pushPullProductIso J M Jm hJm).hom ≫
        (localizationPushforwardPullbackNatIsoSheafHom J M).hom =
    ((pushPullProductIso J N Jn hJn).hom ≫
        (localizationPushforwardPullbackNatIsoSheafHom J N).hom) ≫
      SheafHomAdj.sheafHomContraMap (totSheafify J f)
  rw [← Category.assoc, pushPullRestrictionTransition_comp_pushPullProductIso, Category.assoc,
    localizationPushforwardPullbackNatIsoSheafHom_naturality, ← Category.assoc]

end CategoryTheory.SemiRepresentable

end
