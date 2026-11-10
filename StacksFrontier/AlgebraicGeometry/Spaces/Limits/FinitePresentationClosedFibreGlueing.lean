module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing

/-!
# Glueing algebraic spaces of finite presentation at a closed point

Let `S` be a scheme, let `s` be a point of `S` and let `U` be an open subscheme of `S` whose
underlying set is the complement of `s`. Because the complement of a point and any neighbourhood
of it cover the space, every open neighbourhood `W` of `s` gives a covering of `S` by the two
opens `U` and `W`, so the equivalence of Stacks 0E8Z applies to it: the algebraic spaces of
finite presentation over `S` are the `2`-fibre product `FP_U ×_{FP_{U ∩ W}} FP_W`. That the
complement of `s` is open is where `s` being a closed point is used, and it is the only place.

Stacks 0E90 is the limit of this over the affine open neighbourhoods of `s`: with
`M = Spec 𝒪_{S,s}` the limit of those neighbourhoods and `N = M ∖ {s}` the limit of their
intersections with `U`, the comparison functor `FP_S ⥤ FP_U ×_{FP_N} FP_M` is an equivalence.
This file proves the formal combination: for an object `M` of the big fppf site of `S` equipped
with a cofiltered system of open neighbourhoods `W i` of `s` under it, and an object `N` over
the system of the `W i ∩ U`, such that base change exhibits the algebraic spaces of finite
presentation over `M` as the cofiltered `2`-colimit of those over the `W i` and likewise for `N`
and the `W i ∩ U`, the comparison functor attached to the cartesian square with vertices `N`,
`U`, `M`, `S` is an equivalence. The two colimit identifications are carried as hypotheses; see
the section on what is and is not proved below.

Faithfulness and fullness are transported from a single neighbourhood: two morphisms over `S`
agreeing over `M` already agree over some `W j`, and a morphism of glueing data over `M` comes
from some `W j`, after which its square condition over `N` holds over some `W k ∩ U`; at that
neighbourhood Stacks 0E8Z applies. Essential surjectivity needs in addition that the comparison
isomorphism of a glueing datum descends to a neighbourhood.

All the comparison isomorphisms used are pinned: base change along a composite is compared with
the iterated base change by the uniqueness of a pullback, so each comparison is determined by
its composites with the projections, and the coherence identities between them — associativity
of the comparisons of a factorisation, compatibility of the comparison of a square with a
comparison of two squares, and the horizontal pasting of two squares — are proved by checking
those projections in the slice of presheaves.

## Main definitions

* `CategoryTheory.Over.pullbackFactorObjIso` and `CategoryTheory.Over.pullbackFactorIso`: the
  comparison between base change along `c` and the iterated base change along a factorisation
  `c = a ≫ b`, at an object and naturally in it.
* `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso`: the same comparison for
  the categories of algebraic spaces of finite presentation.
* `AlgebraicGeometry.FinitePresentationSpacesOver.toBase`: the canonical morphism of an object
  of the big fppf category over `S` to the canonical terminal object, namely the base itself.
* `AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`: the property
  that base change along a cone exhibits the algebraic spaces of finite presentation over the
  vertex as the cofiltered `2`-colimit of those over the stages. This is the shape of the two
  carried hypotheses.
* `AlgebraicGeometry.FinitePresentationSpacesOver.coneIso` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.transIso`: the comparisons of base change from
  the base to the vertex, respectively to a stage, with base change through a stage,
  respectively through an earlier stage.

The comparison functor of Stacks 0E90 itself is not a new definition: it is
`AlgebraicGeometry.FinitePresentationSpacesOver.glueingFunctor B S hS hsq.w` of
`StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSlice`, for `hsq` the cartesian square
with vertices `N`, `U`, `M` and the base, which takes an algebraic space of finite presentation
over `S` to its base changes to `U` and to `M` together with the canonical identification of
their further base changes to `N`.

## Main results

* `AlgebraicGeometry.isOpen_compl_singleton_of_mem_closedPoints`,
  `AlgebraicGeometry.mem_union_of_eq_compl_singleton` and
  `AlgebraicGeometry.sup_eq_top_of_eq_compl_singleton`: the point-set lemma. The complement of a
  closed point is open, and together with any neighbourhood of the point it covers the space.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_compl_singleton`:
  **the equivalence of Stacks 0E8Z at a single open neighbourhood of the point**, with no
  hypothesis beyond the point-set situation. This is the step of Stacks 0E90 that is proved
  outright.
* `CategoryTheory.Over.pullbackFactorObjIso_assoc`,
  `CategoryTheory.Over.pullbackSquareObjIso_comp_map` and
  `CategoryTheory.Over.pullbackSquareObjIso_paste`, and their counterparts
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso_assoc`,
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_comp_map` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeSquareIso_paste`: the three
  coherence identities between the pinned comparison isomorphisms.
* `AlgebraicGeometry.FinitePresentationSpacesOver.representsOverM_of_full` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.representsOverM_trans`: a morphism found at a
  stage base changes to the given morphism over the vertex, and this property transports to a
  later stage.
* `AlgebraicGeometry.FinitePresentationSpacesOver.squareCondition_iff` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.squareCondition_of_stage`: the square
  condition of the `2`-fibre product transfers along a comparison of two cartesian squares.
* `AlgebraicGeometry.FinitePresentationSpacesOver.faithful_glueingFunctor_of_colimit`,
  `AlgebraicGeometry.FinitePresentationSpacesOver.full_glueingFunctor_of_colimit` and
  `AlgebraicGeometry.FinitePresentationSpacesOver.essSurj_glueingFunctor_of_colimit`: the
  comparison functor is faithful, full and essentially surjective.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_colimit`:
  **the comparison functor is an equivalence**, which is Stacks 0E90 granted the two colimit
  identifications.

## What is proved of Stacks 0E90, and what is not

Proved with no hypothesis beyond the point-set situation: that the complement of the closed
point `s` and any open neighbourhood `W` of it cover `S`, and hence that the comparison functor
`FP_S ⥤ FP_U ×_{FP_{U ∩ W}} FP_W` of Stacks 0E8Z is an equivalence for every such `W`. This is
the first half of the argument of Stacks 0E90.

Proved from two hypotheses: that the comparison functor `FP_S ⥤ FP_U ×_{FP_N} FP_M` is an
equivalence. The hypotheses are

* `hloc : IsFinitePresentationColimit B S hS W M pM hpM`, that base change along the cone `pM`
  exhibits `FP_M` as the cofiltered `2`-colimit of the `FP_{W i}`, and
* `hoverlap : IsFinitePresentationColimit B S hS Wn N pN hpN`, the same for `FP_N` and the
  `FP_{W i ∩ U}`,

together with the data these refer to: the index category, the two diagrams, the two cones and
the evident compatibilities of the cones with the structure morphisms of the squares.

Not proved, and the reason the two hypotheses are carried: the theorem never says that `M` is
`Spec 𝒪_{S,s}` or that `N` is its puncture — `M` and `N` are arbitrary objects of the site with
the stated colimit property. Specialising the theorem to Stacks 0E90 requires the cofiltered
diagram of affine open neighbourhoods of `s`, the identification of `Spec 𝒪_{S,s}` with its
limit, and the identification of `Spec 𝒪_{S,s} ∖ {s}` with the limit of the `W i ∩ U` — which
are quasi-compact because `U → S` is, the hypothesis of Stacks 0E90 that plays no other role
here. Those limit identifications are not available in this library for the big fppf site, and
they are not constructed here. Granted them, the two hypotheses are exactly what
Stacks 07SK provides: `AlgebraicGeometry.Space.exists_model_of_finitePresentation` (essential
surjectivity), `AlgebraicGeometry.Space.exists_morphism_after_baseChange` (fullness) and
`AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq` (faithfulness) of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent`, which are stated for a
cofiltered diagram of presheaves with affine transitions and its limit; transporting them from
that formulation to base change along a cone is likewise not done here.

The fourth condition `IsFinitePresentationColimit.essIso`, that an isomorphism between the base
changes of two stage objects descends to an isomorphism at a stage, is a consequence of the
fullness and faithfulness conditions by a cofiltered argument; it is carried as a separate
condition rather than derived from them, so that the cofiltered bookkeeping — composing
transition morphisms and comparing the iterated base changes with the base change along the
composite — is avoided. Like the other three it is a statement about the colimit identification
alone: none of the four mentions the terminal object of the site, the category of algebraic
spaces of finite presentation over it, or the comparison functor whose being an equivalence is
the conclusion.

## Implementation notes

The maps to the base are the unique maps to the canonical terminal object `Over.mk (𝟙 (B.obj
hS))` of the big fppf category over `S`, so every compatibility of a cone or a transition
morphism with the structure morphisms to the base holds by terminality and none of them has to
be carried as a hypothesis. For the same reason the point-set hypothesis is needed only in the
form that reads the ranges in `S`.

A comparison isomorphism between two iterated base changes computing the same pullback is built
here from `CategoryTheory.IsPullback.isoIsPullback`, whose characterising equations are its
compatibilities with the two projections; the comparison of a commutative square is Mathlib's,
through `CategoryTheory.Over.pullbackSquareIso` of
`StacksFrontier.AlgebraicGeometry.RestrictionComparison.OverSquare`, which is built the same way.
Consequently every coherence identity between them is proved by one recipe: transport to the
slice of presheaves along the fully faithful inclusion of the full subcategory, reduce to the
underlying morphisms of the slice, and check the composites with the chain of projections of the
iterated pullback, the remaining projection being forced by the structure morphisms. The
restatements whose names end in `_pullback_obj` are the pinning lemmas at a base change, in the
form in which they apply after `simp` has unfolded the structure morphism of that base change.

The colimit conditions are stated elementarily, as conditions on the family of base-change
functors, rather than as a limit in a category of categories; this is the form in which
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent` states Stacks 07SK, and
it needs no strict diagram of base-change functors. The comparison isomorphisms that the
conditions refer to are the pinned ones, so no choice is left open in them.

## References

* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C] {X Y T : C} {a : X ⟶ Y} {b : Y ⟶ T}
  {c : X ⟶ T}

/-- Pulling `A : Over T` back along `b` and then along `a` computes the pullback of `A.hom`
along a factorisation `c = a ≫ b`. -/
theorem isPullback_pullback_snd_pullback_of_comp (h : a ≫ b = c) (A : Over T) :
    IsPullback (pullback.fst (pullback.snd A.hom b) a ≫ pullback.fst A.hom b)
      (pullback.snd (pullback.snd A.hom b) a) A.hom c := by
  rw [← h]
  exact isPullback_pullback_snd_pullback A

/-- The comparison isomorphism, at a single object of `Over T`, between base change along `c`
and the iterated base change along a factorisation `c = a ≫ b` of it. -/
noncomputable def pullbackFactorObjIso (h : a ≫ b = c) (A : Over T) :
    (Over.pullback c).obj A ≅ (Over.pullback b ⋙ Over.pullback a).obj A :=
  Over.isoMk ((IsPullback.of_hasPullback A.hom c).isoIsPullback _ _
    (isPullback_pullback_snd_pullback_of_comp h A)) (by simp)

@[reassoc (attr := simp)]
theorem pullbackFactorObjIso_hom_left_fst (h : a ≫ b = c) (A : Over T) :
    (pullbackFactorObjIso h A).hom.left ≫ pullback.fst (pullback.snd A.hom b) a ≫
        pullback.fst A.hom b =
      pullback.fst A.hom c :=
  (IsPullback.of_hasPullback A.hom c).isoIsPullback_hom_fst _ _
    (isPullback_pullback_snd_pullback_of_comp h A)

@[reassoc (attr := simp)]
theorem pullbackFactorObjIso_hom_left_snd (h : a ≫ b = c) (A : Over T) :
    (pullbackFactorObjIso h A).hom.left ≫ pullback.snd (pullback.snd A.hom b) a =
      pullback.snd A.hom c :=
  (IsPullback.of_hasPullback A.hom c).isoIsPullback_hom_snd _ _
    (isPullback_pullback_snd_pullback_of_comp h A)

/-- Base change along `c` is isomorphic to the iterated base change along a factorisation
`c = a ≫ b` of it, naturally in the object pulled back. -/
noncomputable def pullbackFactorIso (h : a ≫ b = c) :
    Over.pullback c ≅ Over.pullback b ⋙ Over.pullback a :=
  NatIso.ofComponents (pullbackFactorObjIso h) (by
    intro A A' f
    ext
    apply (isPullback_pullback_snd_pullback_of_comp h A').hom_ext
    · simp [Over.pullback_obj_hom, Over.pullback_obj_left]
    · simp [Over.pullback_obj_hom, Over.pullback_obj_left])

@[simp]
theorem pullbackFactorIso_hom_app (h : a ≫ b = c) (A : Over T) :
    (pullbackFactorIso h).hom.app A = (pullbackFactorObjIso h A).hom :=
  rfl

/-- The compatibility of the comparison isomorphism of a factorisation with the projections,
at a base change: the form in which it applies after the structure morphism of a base change
has been unfolded. -/
@[reassoc (attr := simp)]
theorem pullbackFactorObjIso_hom_left_fst_pullback_obj {X₁ X₂ X₃ X₄ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {fg : X₁ ⟶ X₃} (hfg : f ≫ g = fg) (k : X₃ ⟶ X₄) (A : Over X₄) :
    (pullbackFactorObjIso hfg ((Over.pullback k).obj A)).hom.left ≫
        pullback.fst (pullback.snd (pullback.snd A.hom k) g) f ≫
          pullback.fst (pullback.snd A.hom k) g =
      pullback.fst (pullback.snd A.hom k) fg :=
  pullbackFactorObjIso_hom_left_fst hfg ((Over.pullback k).obj A)

/-- The compatibility of the comparison isomorphism of a factorisation with the projections to
the base, at a base change. -/
@[reassoc (attr := simp)]
theorem pullbackFactorObjIso_hom_left_snd_pullback_obj {X₁ X₂ X₃ X₄ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {fg : X₁ ⟶ X₃} (hfg : f ≫ g = fg) (k : X₃ ⟶ X₄) (A : Over X₄) :
    (pullbackFactorObjIso hfg ((Over.pullback k).obj A)).hom.left ≫
        pullback.snd (pullback.snd (pullback.snd A.hom k) g) f =
      pullback.snd (pullback.snd A.hom k) fg :=
  pullbackFactorObjIso_hom_left_snd hfg ((Over.pullback k).obj A)

/-- Pulling `A : Over X₄` back along `k`, then along `g`, then along `f` computes the pullback
of `A.hom` along a factorisation of a morphism into three factors. -/
theorem isPullback_pullback_snd_pullback_snd_pullback_of_comp {X₁ X₂ X₃ X₄ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {k : X₃ ⟶ X₄} {fg : X₁ ⟶ X₃} {fgk : X₁ ⟶ X₄} (hfg : f ≫ g = fg)
    (h : fg ≫ k = fgk) (A : Over X₄) :
    IsPullback ((pullback.fst (pullback.snd ((Over.pullback k).obj A).hom g) f ≫
        pullback.fst ((Over.pullback k).obj A).hom g) ≫ pullback.fst A.hom k)
      (pullback.snd (pullback.snd ((Over.pullback k).obj A).hom g) f) A.hom fgk := by
  rw [← h]
  exact (isPullback_pullback_snd_pullback_of_comp hfg ((Over.pullback k).obj A)).paste_horiz
    (IsPullback.of_hasPullback A.hom k)

/-- Two morphisms into a triple base change of `A` are equal when they agree after the
projections to `A` and to the last pulled-back object. -/
private theorem hom_ext_pullback_pullback_pullback {X₁ X₂ X₃ X₄ : C} {f : X₁ ⟶ X₂}
    {g : X₂ ⟶ X₃} {k : X₃ ⟶ X₄} (A : Over X₄) {Z : Over X₁}
    {u v : Z ⟶ (Over.pullback f).obj ((Over.pullback g).obj ((Over.pullback k).obj A))}
    (h₁ : u.left ≫ (pullback.fst (pullback.snd ((Over.pullback k).obj A).hom g) f ≫
        pullback.fst ((Over.pullback k).obj A).hom g) ≫ pullback.fst A.hom k =
      v.left ≫ (pullback.fst (pullback.snd ((Over.pullback k).obj A).hom g) f ≫
        pullback.fst ((Over.pullback k).obj A).hom g) ≫ pullback.fst A.hom k)
    (h₂ : u.left ≫ pullback.snd (pullback.snd ((Over.pullback k).obj A).hom g) f =
      v.left ≫ pullback.snd (pullback.snd ((Over.pullback k).obj A).hom g) f) : u = v := by
  apply Over.OverMorphism.ext
  exact (isPullback_pullback_snd_pullback_snd_pullback_of_comp (f := f) (g := g) (k := k)
    rfl rfl A).hom_ext h₁ h₂

/-- **The comparison isomorphisms of factorisations are associative.** Splitting base change
along `f ≫ g ≫ k` into three steps in either order gives the same comparison. -/
theorem pullbackFactorObjIso_assoc {X₁ X₂ X₃ X₄ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {k : X₃ ⟶ X₄}
    {fg : X₁ ⟶ X₃} {gk : X₂ ⟶ X₄} {fgk : X₁ ⟶ X₄} (hfg : f ≫ g = fg) (hgk : g ≫ k = gk)
    (h₁ : f ≫ gk = fgk) (h₂ : fg ≫ k = fgk) (A : Over X₄) :
    (pullbackFactorObjIso h₁ A).hom ≫ (Over.pullback f).map (pullbackFactorObjIso hgk A).hom =
      (pullbackFactorObjIso h₂ A).hom ≫
        (pullbackFactorObjIso hfg ((Over.pullback k).obj A)).hom := by
  apply hom_ext_pullback_pullback_pullback A <;>
    simp

/-- The compatibility of the comparison isomorphism of a cartesian square with the projections
to the object pulled back, at a base change. -/
@[reassoc (attr := simp)]
theorem pullbackSquareObjIso_hom_left_fst_pullback_obj {S' U' L' V' Z' : C} {u : U' ⟶ S'}
    {p : L' ⟶ S'} {v : V' ⟶ L'} {q : V' ⟶ U'} (w : q ≫ u = v ≫ p) (k : S' ⟶ Z')
    (A : Over Z') :
    (pullbackSquareObjIso w ((Over.pullback k).obj A)).hom.left ≫
        pullback.fst (pullback.snd (pullback.snd A.hom k) p) v ≫
          pullback.fst (pullback.snd A.hom k) p =
      pullback.fst (pullback.snd (pullback.snd A.hom k) u) q ≫
        pullback.fst (pullback.snd A.hom k) u :=
  pullbackSquareObjIso_hom_left_fst w ((Over.pullback k).obj A)

/-- The compatibility of the comparison isomorphism of a cartesian square with the projections
to the fourth vertex, at a base change. -/
@[reassoc (attr := simp)]
theorem pullbackSquareObjIso_hom_left_snd_pullback_obj {S' U' L' V' Z' : C} {u : U' ⟶ S'}
    {p : L' ⟶ S'} {v : V' ⟶ L'} {q : V' ⟶ U'} (w : q ≫ u = v ≫ p) (k : S' ⟶ Z')
    (A : Over Z') :
    (pullbackSquareObjIso w ((Over.pullback k).obj A)).hom.left ≫
        pullback.snd (pullback.snd (pullback.snd A.hom k) p) v =
      pullback.snd (pullback.snd (pullback.snd A.hom k) u) q :=
  pullbackSquareObjIso_hom_left_snd w ((Over.pullback k).obj A)

/-- **The comparison isomorphisms of two cartesian squares over the same morphism are
compatible with a comparison of the squares.** -/
theorem pullbackSquareObjIso_comp_map {Z' U' M₁ M₂ N₁ N₂ : C} {jU : U' ⟶ Z'} {jW₁ : M₁ ⟶ Z'}
    {jW₂ : M₂ ⟶ Z'} {iU₁ : N₁ ⟶ U'} {iW₁ : N₁ ⟶ M₁} {iU₂ : N₂ ⟶ U'} {iW₂ : N₂ ⟶ M₂}
    {r : N₁ ⟶ N₂} {t : M₁ ⟶ M₂} (w₁ : iU₁ ≫ jU = iW₁ ≫ jW₁) (w₂ : iU₂ ≫ jU = iW₂ ≫ jW₂)
    (c₁ : r ≫ iU₂ = iU₁) (c₂ : r ≫ iW₂ = iW₁ ≫ t) (c₃ : t ≫ jW₂ = jW₁) (A : Over Z') :
    (pullbackSquareObjIso w₁ A).hom ≫
        (Over.pullback iW₁).map (pullbackFactorObjIso c₃ A).hom =
      (pullbackFactorObjIso c₁ ((Over.pullback jU).obj A)).hom ≫
        (Over.pullback r).map (pullbackSquareObjIso w₂ A).hom ≫
          (pullbackSquareObjIso c₂ ((Over.pullback jW₂).obj A)).hom := by
  apply hom_ext_pullback_pullback_pullback A <;>
    simp

/-- **Pasting two cartesian squares horizontally is compatible with the comparison
isomorphisms.** The comparison of the pasted square is the composite of the comparison of the
second square, the base change of the comparison of the first, and the comparisons of the two
factorisations. -/
theorem pullbackSquareObjIso_paste {N' Wni Wnj Wi Wj M' : C} {pNi : N' ⟶ Wni} {pNj : N' ⟶ Wnj}
    {wne : Wnj ⟶ Wni} {iWni : Wni ⟶ Wi} {iWnj : Wnj ⟶ Wj} {we : Wj ⟶ Wi} {iM : N' ⟶ M'}
    {pMi : M' ⟶ Wi} {pMj : M' ⟶ Wj} (h₁ : pNj ≫ wne = pNi) (h₂ : wne ≫ iWni = iWnj ≫ we)
    (h₃ : pNi ≫ iWni = iM ≫ pMi) (h₄ : pNj ≫ iWnj = iM ≫ pMj) (h₅ : pMj ≫ we = pMi)
    (A : Over Wi) :
    (pullbackFactorObjIso h₁ ((Over.pullback iWni).obj A)).hom ≫
        (Over.pullback pNj).map (pullbackSquareObjIso h₂ A).hom ≫
          (pullbackSquareObjIso h₄ ((Over.pullback we).obj A)).hom =
      (pullbackSquareObjIso h₃ A).hom ≫
        (Over.pullback iM).map (pullbackFactorObjIso h₅ A).hom := by
  apply hom_ext_pullback_pullback_pullback A <;>
    simp

end CategoryTheory.Over

namespace AlgebraicGeometry

/-! ### The point-set lemma -/

/-- The complement of a closed point is open. -/
theorem isOpen_compl_singleton_of_mem_closedPoints {X : Type u} [TopologicalSpace X] {s : X}
    (hs : s ∈ closedPoints X) : IsOpen ({s}ᶜ : Set X) :=
  (mem_closedPoints_iff.1 hs).isOpen_compl

/-- **The complement of a point and any neighbourhood of it cover the space.** -/
theorem mem_union_of_eq_compl_singleton {X : Type u} {s : X} {U W : Set X} (hU : U = {s}ᶜ)
    (hW : s ∈ W) (x : X) : x ∈ U ∨ x ∈ W := by
  subst hU
  by_cases h : x = s
  · exact Or.inr (h ▸ hW)
  · exact Or.inl h

/-- **The complement of a point and any open neighbourhood of it cover a scheme.** -/
theorem sup_eq_top_of_eq_compl_singleton {S : Scheme.{u}} {s : S} {U W : S.Opens}
    (hU : (U : Set S) = {s}ᶜ) (hW : s ∈ W) : U ⊔ W = ⊤ := by
  apply le_antisymm le_top
  intro x _
  exact mem_union_of_eq_compl_singleton hU hW x

namespace FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The equivalence at a single neighbourhood of the point -/

section Stage

variable {U W V : BigFppfOver B S hS} {s : S}
  {jU : U ⟶ Over.mk (𝟙 (B.obj hS))} {jW : W ⟶ Over.mk (𝟙 (B.obj hS))}

/-- A morphism of the big fppf category over `S` to the canonical terminal object is the
structure morphism of its source. -/
theorem toScheme_map_eq_inclusion_map_hom (jU : U ⟶ Over.mk (𝟙 (B.obj hS))) :
    (BigFppfOver.toScheme B S hS).map jU = B.inclusion.map U.hom := by
  rw [Over.mkIdTerminal.hom_ext jU (Over.mkIdTerminal.from U)]
  exact toScheme_map_mkIdTerminal_from B S hS U

/-- **The equivalence of Stacks 0E8Z at a single open neighbourhood of the point.** -/
theorem isEquivalence_glueingFunctor_of_compl_singleton
    {iU : V ⟶ U} {iW : V ⟶ W} (hV : IsPullback iU iW jU jW)
    (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
    (hWopen : IsOpenImmersion (B.inclusion.map W.hom))
    (hU : Set.range (B.inclusion.map U.hom) = {s}ᶜ)
    (hW : s ∈ Set.range (B.inclusion.map W.hom)) :
    (glueingFunctor B S hS hV.w).IsEquivalence := by
  have key : ∀ {X : BigFppfOver B S hS} (j : X ⟶ Over.mk (𝟙 (B.obj hS))),
      IsOpenImmersion (B.inclusion.map X.hom) →
        Mono j ∧ IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) := fun j h => by
    rw [toScheme_map_eq_inclusion_map_hom]
    exact ⟨(BigFppfOver.toScheme B S hS).mono_of_mono_map
      (by rw [toScheme_map_eq_inclusion_map_hom]; infer_instance), h⟩
  have hcov := fun x => mem_union_of_eq_compl_singleton hU hW x
  obtain ⟨hmU, hjU⟩ := key jU hUopen
  obtain ⟨hmW, hjW⟩ := key jW hWopen
  exact isEquivalence_glueingFunctor B S hS Over.mkIdTerminal hV hjU hjW
    (by rwa [toScheme_map_eq_inclusion_map_hom, toScheme_map_eq_inclusion_map_hom])
    hUopen hWopen hcov

end Stage

/-! ### Base change along a factorisation -/

/-- The comparison isomorphism between base change along `c` and the composite of the base
changes along a factorisation `c = a ≫ b` of it. It is the comparison of
`CategoryTheory.Over.pullbackFactorIso`, which is pinned by its compatibility with the
projections to the object pulled back, transported into the full subcategories along the fully
faithful inclusion. -/
noncomputable def baseChangeFactorIso {X Y T : BigFppfOver B S hS} {a : X ⟶ Y} {b : Y ⟶ T}
    {c : X ⟶ T} (h : a ≫ b = c) :
    baseChange B S hS c ≅ baseChange B S hS b ⋙ baseChange B S hS a :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X))
    (Functor.isoWhiskerLeft (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS T))
      (Over.pullbackFactorIso (by rw [← Functor.map_comp, h])))

/-- The comparison isomorphism of a factorisation is the one of
`CategoryTheory.Over.pullbackFactorIso`, read in the slice of presheaves. -/
theorem baseChangeFactorIso_hom_app_left {X Y T : BigFppfOver B S hS} {a : X ⟶ Y} {b : Y ⟶ T}
    {c : X ⟶ T} (h : a ≫ b = c) (A : FinitePresentationSpacesOver B S hS T) :
    (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X)).map
        ((baseChangeFactorIso B S hS h).hom.app A) =
      (Over.pullbackFactorIso (a := yoneda.map a) (b := yoneda.map b) (c := yoneda.map c)
        (by rw [← Functor.map_comp, h])).hom.app A.obj :=
  Functor.map_preimage _ _

/-- Two morphisms with the same image under a functor have the same image under any functor
isomorphic to it. -/
theorem map_eq_of_natIso {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (ν : F ≅ G) {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g) :
    G.map f = G.map g := by
  rw [← NatIso.naturality_1 ν f, ← NatIso.naturality_1 ν g, h]

/-- **The comparison isomorphisms of factorisations are associative**: splitting base change
along `abc = a ≫ b ≫ c` into three steps in either order gives the same comparison. -/
theorem baseChangeFactorIso_assoc {X₁ X₂ X₃ X₄ : BigFppfOver B S hS} {a : X₁ ⟶ X₂}
    {b : X₂ ⟶ X₃} {c : X₃ ⟶ X₄} {ab : X₁ ⟶ X₃} {bc : X₂ ⟶ X₄} {abc : X₁ ⟶ X₄}
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc) (h₁ : a ≫ bc = abc) (h₂ : ab ≫ c = abc)
    (A : FinitePresentationSpacesOver B S hS X₄) :
    (baseChangeFactorIso B S hS h₁).hom.app A ≫
        (baseChange B S hS a).map ((baseChangeFactorIso B S hS hbc).hom.app A) =
      (baseChangeFactorIso B S hS h₂).hom.app A ≫
        (baseChangeFactorIso B S hS hab).hom.app ((baseChange B S hS c).obj A) := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS X₁)).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, baseChangeFactorIso_hom_app_left,
    baseChangeFactorIso_hom_app_left, ι_map_baseChange_map, baseChangeFactorIso_hom_app_left,
    baseChangeFactorIso_hom_app_left]
  exact Over.pullbackFactorObjIso_assoc (by rw [← Functor.map_comp, hab])
    (by rw [← Functor.map_comp, hbc]) (by rw [← Functor.map_comp, h₁])
    (by rw [← Functor.map_comp, h₂]) A.obj

/-- **The comparison isomorphisms of two cartesian squares over the same morphism `jU` are
compatible with a comparison `(r, t)` of the two squares.** Base changing the comparison of the
second square along `r` and composing with the comparisons of the factorisations recovers the
comparison of the first square. -/
theorem baseChangeSquareIso_comp_map {Z' U' M₁ M₂ N₁ N₂ : BigFppfOver B S hS} {jU : U' ⟶ Z'}
    {jW₁ : M₁ ⟶ Z'} {jW₂ : M₂ ⟶ Z'} {iU₁ : N₁ ⟶ U'} {iW₁ : N₁ ⟶ M₁} {iU₂ : N₂ ⟶ U'}
    {iW₂ : N₂ ⟶ M₂} {r : N₁ ⟶ N₂} {t : M₁ ⟶ M₂} (w₁ : iU₁ ≫ jU = iW₁ ≫ jW₁)
    (w₂ : iU₂ ≫ jU = iW₂ ≫ jW₂) (c₁ : r ≫ iU₂ = iU₁) (c₂ : r ≫ iW₂ = iW₁ ≫ t)
    (c₃ : t ≫ jW₂ = jW₁) (A : FinitePresentationSpacesOver B S hS Z') :
    (baseChangeSquareIso B S hS w₁).hom.app A ≫
        (baseChange B S hS iW₁).map ((baseChangeFactorIso B S hS c₃).hom.app A) =
      (baseChangeFactorIso B S hS c₁).hom.app ((baseChange B S hS jU).obj A) ≫
        (baseChange B S hS r).map ((baseChangeSquareIso B S hS w₂).hom.app A) ≫
          (baseChangeSquareIso B S hS c₂).hom.app ((baseChange B S hS jW₂).obj A) := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N₁)).map_injective ?_
  simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
    baseChangeFactorIso_hom_app_left]
  exact Over.pullbackSquareObjIso_comp_map
    (by rw [← Functor.map_comp, ← Functor.map_comp, w₁])
    (by rw [← Functor.map_comp, ← Functor.map_comp, w₂])
    (by rw [← Functor.map_comp, c₁]) (by rw [← Functor.map_comp, ← Functor.map_comp, c₂])
    (by rw [← Functor.map_comp, c₃]) A.obj

/-! ### The categories of finite-presentation spaces over a cofiltered system -/

/-- The canonical morphism of an object of the big fppf category over `S` to the canonical
terminal object, namely the base itself. -/
noncomputable abbrev toBase (X : BigFppfOver B S hS) : X ⟶ Over.mk (𝟙 (B.obj hS)) :=
  Over.mkIdTerminal.from X

/-- **Base change exhibits the finite-presentation algebraic spaces over `M` as the cofiltered
`2`-colimit of those over the stages of a cofiltered system `W` under `M`.** The conditions are
essential surjectivity, fullness and faithfulness of the family of base-change functors along
the cone `p`, in the elementary form in which a filtered colimit of categories is expressed:
every object over `M` comes from a stage, every morphism between objects coming from a stage
comes from a later stage, and two morphisms of a stage that agree over `M` already agree at a
later stage; together with the isomorphism form of the second and third, which follows from
them but is carried separately. -/
structure IsFinitePresentationColimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (W : I ⥤ BigFppfOver B S hS) (M : BigFppfOver B S hS)
    (p : (i : I) → (M ⟶ W.obj i)) (hp : ∀ {i j : I} (e : j ⟶ i), p j ≫ W.map e = p i) :
    Prop where
  /-- Every algebraic space of finite presentation over `M` is, up to isomorphism, the base
  change of one over a stage. -/
  essSurj : ∀ Y : FinitePresentationSpacesOver B S hS M, ∃ (i : I)
    (Yi : FinitePresentationSpacesOver B S hS (W.obj i)),
    Nonempty ((baseChange B S hS (p i)).obj Yi ≅ Y)
  /-- A morphism between the base changes to `M` of two spaces over a stage is the base change
  of a morphism at a later stage. -/
  full : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
    (h : (baseChange B S hS (p i)).obj X ⟶ (baseChange B S hS (p i)).obj Y),
    ∃ (j : I) (e : j ⟶ i) (h' : (baseChange B S hS (W.map e)).obj X ⟶
      (baseChange B S hS (W.map e)).obj Y),
      (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map h' =
        h ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y
  /-- An isomorphism between the base changes to `M` of two spaces over a stage is, up to the
  comparisons of the factorisations, the base change of an isomorphism at a later stage. This
  is the isomorphism form of `full` and `faithful`, which it follows from by a cofiltered
  argument. -/
  essIso : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i))
    (Θ : (baseChange B S hS (p i)).obj X ≅ (baseChange B S hS (p i)).obj Y),
    ∃ (j : I) (e : j ⟶ i) (Θ' : (baseChange B S hS (W.map e)).obj X ≅
      (baseChange B S hS (W.map e)).obj Y),
      (baseChangeFactorIso B S hS (hp e)).hom.app X ≫ (baseChange B S hS (p j)).map Θ'.hom =
        Θ.hom ≫ (baseChangeFactorIso B S hS (hp e)).hom.app Y
  /-- Two morphisms of spaces over a stage whose base changes to `M` agree already agree at a
  later stage. -/
  faithful : ∀ (i : I) (X Y : FinitePresentationSpacesOver B S hS (W.obj i)) (f g : X ⟶ Y),
    (baseChange B S hS (p i)).map f = (baseChange B S hS (p i)).map g →
    ∃ (j : I) (e : j ⟶ i),
      (baseChange B S hS (W.map e)).map f = (baseChange B S hS (W.map e)).map g

/-- **Pasting two cartesian squares horizontally is compatible with the comparison
isomorphisms**, read in the categories of algebraic spaces of finite presentation. -/
theorem baseChangeSquareIso_paste {N' Wni Wnj Wi Wj M' : BigFppfOver B S hS} {pNi : N' ⟶ Wni}
    {pNj : N' ⟶ Wnj} {wne : Wnj ⟶ Wni} {iWni : Wni ⟶ Wi} {iWnj : Wnj ⟶ Wj} {we : Wj ⟶ Wi}
    {iM : N' ⟶ M'} {pMi : M' ⟶ Wi} {pMj : M' ⟶ Wj} (h₁ : pNj ≫ wne = pNi)
    (h₂ : wne ≫ iWni = iWnj ≫ we) (h₃ : pNi ≫ iWni = iM ≫ pMi) (h₄ : pNj ≫ iWnj = iM ≫ pMj)
    (h₅ : pMj ≫ we = pMi) (A : FinitePresentationSpacesOver B S hS Wi) :
    (baseChangeFactorIso B S hS h₁).hom.app ((baseChange B S hS iWni).obj A) ≫
        (baseChange B S hS pNj).map ((baseChangeSquareIso B S hS h₂).hom.app A) ≫
          (baseChangeSquareIso B S hS h₄).hom.app ((baseChange B S hS we).obj A) =
      (baseChangeSquareIso B S hS h₃).hom.app A ≫
        (baseChange B S hS iM).map ((baseChangeFactorIso B S hS h₅).hom.app A) := by
  refine (ObjectProperty.ι (IsFinitePresentationSpaceOver B S hS N')).map_injective ?_
  simp only [Functor.map_comp, baseChangeSquareIso_hom_app_left, ι_map_baseChange_map,
    baseChangeFactorIso_hom_app_left]
  exact Over.pullbackSquareObjIso_paste (by rw [← Functor.map_comp, h₁])
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₂])
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₃])
    (by rw [← Functor.map_comp, ← Functor.map_comp, h₄]) (by rw [← Functor.map_comp, h₅]) A.obj

/-! ### Comparisons along a cofiltered system under an object -/

/-- The comparison between base change from the base to `M'` and base change to a stage of a
cofiltered system under `M'` followed by base change along the cone. -/
noncomputable abbrev coneIso (M' : BigFppfOver B S hS) {I' : Type u} [Category.{u} I']
    (W' : I' ⥤ BigFppfOver B S hS) (p : (i : I') → (M' ⟶ W'.obj i)) (i : I') :
    baseChange B S hS (toBase B S hS M') ≅
      baseChange B S hS (toBase B S hS (W'.obj i)) ⋙ baseChange B S hS (p i) :=
  baseChangeFactorIso B S hS (Over.mkIdTerminal.hom_ext _ _)

/-- The comparison between base change from the base to a stage and base change to an earlier
stage followed by base change along the transition morphism. -/
noncomputable abbrev transIso {I' : Type u} [Category.{u} I']
    (W' : I' ⥤ BigFppfOver B S hS) {i j : I'} (e : j ⟶ i) :
    baseChange B S hS (toBase B S hS (W'.obj j)) ≅
      baseChange B S hS (toBase B S hS (W'.obj i)) ⋙ baseChange B S hS (W'.map e) :=
  baseChangeFactorIso B S hS (Over.mkIdTerminal.hom_ext _ _)

/-- The three comparisons attached to a stage, an earlier stage and the object `M'` under them
are compatible: this is `AlgebraicGeometry.FinitePresentationSpacesOver.baseChangeFactorIso_assoc`
for the factorisations of the structure morphism of `M'` through the two stages. -/
theorem coneIso_trans {M' : BigFppfOver B S hS} {I' : Type u} [Category.{u} I']
    {W' : I' ⥤ BigFppfOver B S hS} {p : (i : I') → (M' ⟶ W'.obj i)}
    (hp : ∀ {i j : I'} (e : j ⟶ i), p j ≫ W'.map e = p i) {i j : I'} (e : j ⟶ i)
    (A : FinitePresentationSpacesOver B S hS (Over.mk (𝟙 (B.obj hS)))) :
    (coneIso B S hS M' W' p j).hom.app A ≫
        (baseChange B S hS (p j)).map ((transIso B S hS W' e).hom.app A) =
      (coneIso B S hS M' W' p i).hom.app A ≫ (baseChangeFactorIso B S hS (hp e)).hom.app
        ((baseChange B S hS (toBase B S hS (W'.obj i))).obj A) :=
  baseChangeFactorIso_assoc B S hS (hp e) (Over.mkIdTerminal.hom_ext _ _)
    (Over.mkIdTerminal.hom_ext _ _) (Over.mkIdTerminal.hom_ext _ _) A

/-- **A morphism of the base changes to a later stage represents a given morphism over `M'`.**
If `h'` compares the base changes of two stage objects along a transition morphism compatibly
with a morphism over `M'`, then its transport to the later stage base changes to that
morphism. -/
theorem representsOverM_of_full {M' : BigFppfOver B S hS} {I' : Type u} [Category.{u} I']
    {W' : I' ⥤ BigFppfOver B S hS} {p : (i : I') → (M' ⟶ W'.obj i)}
    (hp : ∀ {i j : I'} (e : j ⟶ i), p j ≫ W'.map e = p i)
    {X Y : FinitePresentationSpacesOver B S hS (Over.mk (𝟙 (B.obj hS)))}
    {mR : (baseChange B S hS (toBase B S hS M')).obj X ⟶
      (baseChange B S hS (toBase B S hS M')).obj Y} {i j : I'} (e : j ⟶ i)
    {h' : (baseChange B S hS (W'.map e)).obj
          ((baseChange B S hS (toBase B S hS (W'.obj i))).obj X) ⟶
        (baseChange B S hS (W'.map e)).obj
          ((baseChange B S hS (toBase B S hS (W'.obj i))).obj Y)}
    (hcompat : (baseChangeFactorIso B S hS (hp e)).hom.app
          ((baseChange B S hS (toBase B S hS (W'.obj i))).obj X) ≫
          (baseChange B S hS (p j)).map h' =
        ((coneIso B S hS M' W' p i).inv.app X ≫ mR ≫ (coneIso B S hS M' W' p i).hom.app Y) ≫
          (baseChangeFactorIso B S hS (hp e)).hom.app
            ((baseChange B S hS (toBase B S hS (W'.obj i))).obj Y)) :
    (coneIso B S hS M' W' p j).hom.app X ≫ (baseChange B S hS (p j)).map
        ((transIso B S hS W' e).hom.app X ≫ h' ≫ (transIso B S hS W' e).inv.app Y) =
      mR ≫ (coneIso B S hS M' W' p j).hom.app Y := by
  have hY : (coneIso B S hS M' W' p i).hom.app Y ≫
        (baseChangeFactorIso B S hS (hp e)).hom.app
          ((baseChange B S hS (toBase B S hS (W'.obj i))).obj Y) ≫
          (baseChange B S hS (p j)).map ((transIso B S hS W' e).inv.app Y) =
      (coneIso B S hS M' W' p j).hom.app Y := by
    rw [← Category.assoc, ← coneIso_trans B S hS hp e Y, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
    simp
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, coneIso_trans B S hS hp e X,
    Category.assoc, ← Category.assoc ((baseChangeFactorIso B S hS (hp e)).hom.app _), hcompat,
    Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc, Category.assoc, hY]

/-- The property of base changing to a given morphism over `M'` transports along a transition
morphism to a later stage. -/
theorem representsOverM_trans {M' : BigFppfOver B S hS} {I' : Type u} [Category.{u} I']
    {W' : I' ⥤ BigFppfOver B S hS} {p : (i : I') → (M' ⟶ W'.obj i)}
    (hp : ∀ {i j : I'} (e : j ⟶ i), p j ≫ W'.map e = p i)
    {X Y : FinitePresentationSpacesOver B S hS (Over.mk (𝟙 (B.obj hS)))}
    {mR : (baseChange B S hS (toBase B S hS M')).obj X ⟶
      (baseChange B S hS (toBase B S hS M')).obj Y} {i j : I'} (e : j ⟶ i)
    {g : (baseChange B S hS (toBase B S hS (W'.obj i))).obj X ⟶
      (baseChange B S hS (toBase B S hS (W'.obj i))).obj Y}
    (hg : (coneIso B S hS M' W' p i).hom.app X ≫ (baseChange B S hS (p i)).map g =
      mR ≫ (coneIso B S hS M' W' p i).hom.app Y) :
    (coneIso B S hS M' W' p j).hom.app X ≫ (baseChange B S hS (p j)).map
        ((transIso B S hS W' e).hom.app X ≫ (baseChange B S hS (W'.map e)).map g ≫
          (transIso B S hS W' e).inv.app Y) =
      mR ≫ (coneIso B S hS M' W' p j).hom.app Y := by
  refine representsOverM_of_full B S hS hp e ?_
  have hg' : (baseChange B S hS (p i)).map g =
      (coneIso B S hS M' W' p i).inv.app X ≫ mR ≫ (coneIso B S hS M' W' p i).hom.app Y := by
    rw [← hg, Iso.inv_hom_id_app_assoc]
  rw [← hg']
  exact ((baseChangeFactorIso B S hS (hp e)).hom.naturality g).symm

/-- **The square condition of the `2`-fibre product transfers along a comparison of two
cartesian squares.** Let two cartesian squares over a common morphism `jU` be compared by
`(r, t)`, let `a` be a morphism over `U'`, and let `b₂` over `M₂` base change to `b₁` over `M₁`.
Then the pair `(a, b₁)` satisfies the square condition of the first square if and only if the
base change along `r` of the square condition of `(a, b₂)` for the second square holds. -/
theorem squareCondition_iff {Z' U' M₁ M₂ N₁ N₂ : BigFppfOver B S hS} {jU : U' ⟶ Z'}
    {jW₁ : M₁ ⟶ Z'} {jW₂ : M₂ ⟶ Z'} {iU₁ : N₁ ⟶ U'} {iW₁ : N₁ ⟶ M₁} {iU₂ : N₂ ⟶ U'}
    {iW₂ : N₂ ⟶ M₂} {r : N₁ ⟶ N₂} {t : M₁ ⟶ M₂} (w₁ : iU₁ ≫ jU = iW₁ ≫ jW₁)
    (w₂ : iU₂ ≫ jU = iW₂ ≫ jW₂) (c₁ : r ≫ iU₂ = iU₁) (c₂ : r ≫ iW₂ = iW₁ ≫ t)
    (c₃ : t ≫ jW₂ = jW₁) {X Y : FinitePresentationSpacesOver B S hS Z'}
    {a : (baseChange B S hS jU).obj X ⟶ (baseChange B S hS jU).obj Y}
    {b₁ : (baseChange B S hS jW₁).obj X ⟶ (baseChange B S hS jW₁).obj Y}
    {b₂ : (baseChange B S hS jW₂).obj X ⟶ (baseChange B S hS jW₂).obj Y}
    (hrep : (baseChangeFactorIso B S hS c₃).hom.app X ≫ (baseChange B S hS t).map b₂ =
      b₁ ≫ (baseChangeFactorIso B S hS c₃).hom.app Y) :
    ((baseChange B S hS iU₁).map a ≫ (baseChangeSquareIso B S hS w₁).hom.app Y =
        (baseChangeSquareIso B S hS w₁).hom.app X ≫ (baseChange B S hS iW₁).map b₁) ↔
      (baseChange B S hS r).map ((baseChange B S hS iU₂).map a ≫
          (baseChangeSquareIso B S hS w₂).hom.app Y) =
        (baseChange B S hS r).map ((baseChangeSquareIso B S hS w₂).hom.app X ≫
          (baseChange B S hS iW₂).map b₂) := by
  have hI : (baseChangeFactorIso B S hS c₁).hom.app ((baseChange B S hS jU).obj X) ≫
        (baseChange B S hS r).map ((baseChange B S hS iU₂).map a ≫
            (baseChangeSquareIso B S hS w₂).hom.app Y) ≫
          (baseChangeSquareIso B S hS c₂).hom.app ((baseChange B S hS jW₂).obj Y) =
      (baseChange B S hS iU₁).map a ≫ (baseChangeSquareIso B S hS w₁).hom.app Y ≫
        (baseChange B S hS iW₁).map ((baseChangeFactorIso B S hS c₃).hom.app Y) := by
    have hnat := (baseChangeFactorIso B S hS c₁).hom.naturality a
    simp only [Functor.comp_map] at hnat
    rw [baseChangeSquareIso_comp_map B S hS w₁ w₂ c₁ c₂ c₃ Y, Functor.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hnat]
  have hII : (baseChangeFactorIso B S hS c₁).hom.app ((baseChange B S hS jU).obj X) ≫
        (baseChange B S hS r).map ((baseChangeSquareIso B S hS w₂).hom.app X ≫
            (baseChange B S hS iW₂).map b₂) ≫
          (baseChangeSquareIso B S hS c₂).hom.app ((baseChange B S hS jW₂).obj Y) =
      (baseChangeSquareIso B S hS w₁).hom.app X ≫ (baseChange B S hS iW₁).map b₁ ≫
        (baseChange B S hS iW₁).map ((baseChangeFactorIso B S hS c₃).hom.app Y) := by
    have hnat := (baseChangeSquareIso B S hS c₂).hom.naturality b₂
    simp only [Functor.comp_map] at hnat
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [hnat, ← reassoc_of% (baseChangeSquareIso_comp_map B S hS w₁ w₂ c₁ c₂ c₃ X),
      ← Functor.map_comp, ← Functor.map_comp, hrep]
  constructor
  · intro h
    have key : (baseChangeFactorIso B S hS c₁).hom.app ((baseChange B S hS jU).obj X) ≫
          (baseChange B S hS r).map ((baseChange B S hS iU₂).map a ≫
              (baseChangeSquareIso B S hS w₂).hom.app Y) ≫
            (baseChangeSquareIso B S hS c₂).hom.app ((baseChange B S hS jW₂).obj Y) =
        (baseChangeFactorIso B S hS c₁).hom.app ((baseChange B S hS jU).obj X) ≫
          (baseChange B S hS r).map ((baseChangeSquareIso B S hS w₂).hom.app X ≫
              (baseChange B S hS iW₂).map b₂) ≫
            (baseChangeSquareIso B S hS c₂).hom.app ((baseChange B S hS jW₂).obj Y) := by
      rw [hI, hII, reassoc_of% h]
    exact (Iso.cancel_iso_hom_right _ _ ((baseChangeSquareIso B S hS c₂).app _)).mp
      ((Iso.cancel_iso_hom_left ((baseChangeFactorIso B S hS c₁).app _) _ _).mp key)
  · intro h
    have key : (baseChange B S hS iU₁).map a ≫ (baseChangeSquareIso B S hS w₁).hom.app Y ≫
          (baseChange B S hS iW₁).map ((baseChangeFactorIso B S hS c₃).hom.app Y) =
        (baseChangeSquareIso B S hS w₁).hom.app X ≫ (baseChange B S hS iW₁).map b₁ ≫
          (baseChange B S hS iW₁).map ((baseChangeFactorIso B S hS c₃).hom.app Y) := by
      rw [← hI, ← hII, h]
    rw [← Category.assoc, ← Category.assoc] at key
    exact (Iso.cancel_iso_hom_right _ _
      ((baseChange B S hS iW₁).mapIso ((baseChangeFactorIso B S hS c₃).app Y))).mp key

/-- **The square condition of the `2`-fibre product for a morphism to an arbitrary glueing
datum descends from a stage.** The hypothesis `hrel` says that the comparison `φ` of the datum
is the one induced by the comparison `φj` at the stage. -/
theorem squareCondition_of_stage {Z' U' M₁ M₂ N₁ N₂ : BigFppfOver B S hS} {jU : U' ⟶ Z'}
    {jW₁ : M₁ ⟶ Z'} {jW₂ : M₂ ⟶ Z'} {iU₁ : N₁ ⟶ U'} {iW₁ : N₁ ⟶ M₁} {iU₂ : N₂ ⟶ U'}
    {iW₂ : N₂ ⟶ M₂} {r : N₁ ⟶ N₂} {t : M₁ ⟶ M₂} (w₁ : iU₁ ≫ jU = iW₁ ≫ jW₁)
    (w₂ : iU₂ ≫ jU = iW₂ ≫ jW₂) (c₁ : r ≫ iU₂ = iU₁) (c₂ : r ≫ iW₂ = iW₁ ≫ t)
    (c₃ : t ≫ jW₂ = jW₁) {X : FinitePresentationSpacesOver B S hS Z'}
    {A : FinitePresentationSpacesOver B S hS U'} {Bm : FinitePresentationSpacesOver B S hS M₁}
    {Bj : FinitePresentationSpacesOver B S hS M₂} {a : (baseChange B S hS jU).obj X ⟶ A}
    {bj : (baseChange B S hS jW₂).obj X ⟶ Bj} {χ : (baseChange B S hS t).obj Bj ⟶ Bm}
    {φ : (baseChange B S hS iU₁).obj A ⟶ (baseChange B S hS iW₁).obj Bm}
    {φj : (baseChange B S hS iU₂).obj A ⟶ (baseChange B S hS iW₂).obj Bj}
    (hrel : φ = (baseChangeFactorIso B S hS c₁).hom.app A ≫ (baseChange B S hS r).map φj ≫
      (baseChangeSquareIso B S hS c₂).hom.app Bj ≫ (baseChange B S hS iW₁).map χ)
    (hsqj : (baseChange B S hS iU₂).map a ≫ φj =
      (baseChangeSquareIso B S hS w₂).hom.app X ≫ (baseChange B S hS iW₂).map bj) :
    (baseChange B S hS iU₁).map a ≫ φ =
      (baseChangeSquareIso B S hS w₁).hom.app X ≫ (baseChange B S hS iW₁).map
        ((baseChangeFactorIso B S hS c₃).hom.app X ≫ (baseChange B S hS t).map bj ≫ χ) := by
  have hnat1 := (baseChangeFactorIso B S hS c₁).hom.naturality a
  simp only [Functor.comp_map] at hnat1
  have hnat2 := (baseChangeSquareIso B S hS c₂).hom.naturality bj
  simp only [Functor.comp_map] at hnat2
  rw [hrel, Functor.map_comp, Functor.map_comp]
  rw [reassoc_of% hnat1, ← Functor.map_comp_assoc, hsqj, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat2, ← reassoc_of% (baseChangeSquareIso_comp_map B S hS w₁ w₂ c₁ c₂ c₃ X)]

/-! ### The equivalence at the limit -/

section Limit

variable {U M N : BigFppfOver B S hS} {s : S} {iU : N ⟶ U} {iM : N ⟶ M}
  (hsq : IsPullback iU iM (toBase B S hS U) (toBase B S hS M))
  {I : Type u} [Category.{u} I] [IsCofiltered I] {W Wn : I ⥤ BigFppfOver B S hS}
  {iUn : (i : I) → (Wn.obj i ⟶ U)} {iWn : (i : I) → (Wn.obj i ⟶ W.obj i)}
  (hsqW : ∀ i, IsPullback (iUn i) (iWn i) (toBase B S hS U) (toBase B S hS (W.obj i)))
  {pM : (i : I) → (M ⟶ W.obj i)} {pN : (i : I) → (N ⟶ Wn.obj i)}
  {hpM : ∀ {i j : I} (e : j ⟶ i), pM j ≫ W.map e = pM i}
  {hpN : ∀ {i j : I} (e : j ⟶ i), pN j ≫ Wn.map e = pN i}
  (hpNU : ∀ i, pN i ≫ iUn i = iU) (hpNW : ∀ i, pN i ≫ iWn i = iM ≫ pM i)
  (hiUn : ∀ {i j : I} (e : j ⟶ i), Wn.map e ≫ iUn i = iUn j)
  (hiWn : ∀ {i j : I} (e : j ⟶ i), Wn.map e ≫ iWn i = iWn j ≫ W.map e)
  (hloc : IsFinitePresentationColimit B S hS W M pM hpM)
  (hoverlap : IsFinitePresentationColimit B S hS Wn N pN hpN)
  (hUopen : IsOpenImmersion (B.inclusion.map U.hom))
  (hWopen : ∀ i, IsOpenImmersion (B.inclusion.map (W.obj i).hom))
  (hU : Set.range (B.inclusion.map U.hom) = {s}ᶜ)
  (hW : ∀ i, s ∈ Set.range (B.inclusion.map (W.obj i).hom))

include hsqW hloc hUopen hWopen hU hW in
/-- **The comparison functor of Stacks 0E90 is faithful.** -/
theorem faithful_glueingFunctor_of_colimit :
    (glueingFunctor B S hS hsq.w).Faithful := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  constructor
  intro X Y f g hfg
  have hL : (baseChange B S hS (toBase B S hS U)).map f =
      (baseChange B S hS (toBase B S hS U)).map g := congrArg (fun h => h.hom.left) hfg
  have hR : (baseChange B S hS (toBase B S hS M)).map f =
      (baseChange B S hS (toBase B S hS M)).map g := congrArg (fun h => h.hom.right) hfg
  have hfac : pM i₀ ≫ toBase B S hS (W.obj i₀) = toBase B S hS M :=
    Over.mkIdTerminal.hom_ext _ _
  have hR' := map_eq_of_natIso (baseChangeFactorIso B S hS hfac) hR
  obtain ⟨j, e, hje⟩ := hloc.faithful i₀ _ _
    ((baseChange B S hS (toBase B S hS (W.obj i₀))).map f)
    ((baseChange B S hS (toBase B S hS (W.obj i₀))).map g) hR'
  have hfac2 : W.map e ≫ toBase B S hS (W.obj i₀) = toBase B S hS (W.obj j) :=
    Over.mkIdTerminal.hom_ext _ _
  have hRj : (baseChange B S hS (toBase B S hS (W.obj j))).map f =
      (baseChange B S hS (toBase B S hS (W.obj j))).map g :=
    map_eq_of_natIso (baseChangeFactorIso B S hS hfac2).symm hje
  have hequiv := isEquivalence_glueingFunctor_of_compl_singleton B S hS (hsqW j) hUopen
    (hWopen j) hU (hW j)
  exact (glueingFunctor B S hS (hsqW j).w).map_injective
    (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hL hRj))

include hsqW hpNU hpNW hiUn hiWn hloc hoverlap hUopen hWopen hU hW in
/-- **The comparison functor of Stacks 0E90 is full.** The right component of a morphism of
glueing data comes from a stage by fullness of the colimit over the stages; the square condition
of the `2`-fibre product then holds at a later stage, by faithfulness of the colimit over the
intersections with `U`; and at that stage the comparison functor is full by Stacks 0E8Z. -/
theorem full_glueingFunctor_of_colimit :
    (glueingFunctor B S hS hsq.w).Full := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  constructor
  intro X Y m
  obtain ⟨j, e, h', hcompat⟩ := hloc.full i₀ _ _
    ((coneIso B S hS M W pM i₀).inv.app X ≫ m.hom.right ≫ (coneIso B S hS M W pM i₀).hom.app Y)
  have hrepj := representsOverM_of_full B S hS hpM e hcompat
  set hj := (transIso B S hS W e).hom.app X ≫ h' ≫ (transIso B S hS W e).inv.app Y with hhj
  have hsqj := (squareCondition_iff B S hS hsq.w (hsqW j).w (hpNU j) (hpNW j)
    (Over.mkIdTerminal.hom_ext _ _) hrepj).1 m.hom.w
  obtain ⟨k, e', hk⟩ := hoverlap.faithful j _ _ _ _ hsqj
  have hrepk := representsOverM_trans B S hS hpM e' hrepj
  set hk' := (transIso B S hS W e').hom.app X ≫ (baseChange B S hS (W.map e')).map hj ≫
    (transIso B S hS W e').inv.app Y with hhk
  have hrep' : (transIso B S hS W e').hom.app X ≫ (baseChange B S hS (W.map e')).map hj =
      hk' ≫ (transIso B S hS W e').hom.app Y := by
    rw [hhk]
    simp
  have hsqk := (squareCondition_iff B S hS (hsqW k).w (hsqW j).w (hiUn e') (hiWn e')
    (Over.mkIdTerminal.hom_ext _ _) hrep').2 hk
  have hequiv := isEquivalence_glueingFunctor_of_compl_singleton B S hS (hsqW k) hUopen
    (hWopen k) hU (hW k)
  obtain ⟨f, hf⟩ := (glueingFunctor B S hS (hsqW k).w).map_surjective
    (ObjectProperty.homMk (⟨m.hom.left, hk', hsqk⟩ :
      ((glueingFunctor B S hS (hsqW k).w).obj X).obj ⟶
        ((glueingFunctor B S hS (hsqW k).w).obj Y).obj))
  have hleft : (baseChange B S hS (toBase B S hS U)).map f = m.hom.left :=
    congrArg (fun h => h.hom.left) hf
  have hright : (baseChange B S hS (toBase B S hS (W.obj k))).map f = hk' :=
    congrArg (fun h => h.hom.right) hf
  refine ⟨f, ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hleft ?_)⟩
  rw [glueingFunctor_map_hom_right]
  have hnat := (coneIso B S hS M W pM k).hom.naturality f
  simp only [Functor.comp_map] at hnat
  refine (Iso.cancel_iso_hom_right _ _ ((coneIso B S hS M W pM k).app Y)).mp ?_
  change _ ≫ (coneIso B S hS M W pM k).hom.app Y = _ ≫ (coneIso B S hS M W pM k).hom.app Y
  rw [hnat, hright]
  exact hrepk


include hsqW hpNU hpNW hiUn hiWn hloc hoverlap hUopen hWopen hU hW in
/-- **The comparison functor of Stacks 0E90 is essentially surjective.** The space over `M`
comes from a stage, and the comparison over `N` descends to an isomorphism at a later stage, by
the colimit identifications; at that stage the glueing datum so obtained is the image of a space
over the base by Stacks 0E8Z, and that space has the given datum as its image, because the
comparison of the datum is the one induced by the comparison at the stage. -/
theorem essSurj_glueingFunctor_of_colimit :
    (glueingFunctor B S hS hsq.w).EssSurj := by
  constructor
  intro T
  have hT : IsIso T.obj.hom := T.property
  obtain ⟨i, Bi, ⟨ψ⟩⟩ := hloc.essSurj T.obj.right
  obtain ⟨j, e, θ', hθ'⟩ := hoverlap.essIso i ((baseChange B S hS (iUn i)).obj T.obj.left)
    ((baseChange B S hS (iWn i)).obj Bi)
    ((Iso.app (baseChangeFactorIso B S hS (hpNU i)) T.obj.left).symm ≪≫ asIso T.obj.hom ≪≫
      (baseChange B S hS iM).mapIso ψ.symm ≪≫
      (Iso.app (baseChangeSquareIso B S hS (hpNW i)) Bi).symm)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, asIso_hom,
    Functor.mapIso_hom, Category.assoc] at hθ'
  -- the comparison of the glueing datum at the stage `j`
  set φj := Iso.app (baseChangeFactorIso B S hS (hiUn e)) T.obj.left ≪≫ θ' ≪≫
    Iso.app (baseChangeSquareIso B S hS (hiWn e)) Bi with hφj
  -- the identification of the space over `M` with the base change of the stage object
  set χ := (Iso.app (baseChangeFactorIso B S hS (hpM e)) Bi).symm ≪≫ ψ with hχ
  have hrel : T.obj.hom = (baseChangeFactorIso B S hS (hpNU j)).hom.app T.obj.left ≫
      (baseChange B S hS (pN j)).map φj.hom ≫
        (baseChangeSquareIso B S hS (hpNW j)).hom.app ((baseChange B S hS (W.map e)).obj Bi) ≫
          (baseChange B S hS iM).map χ.hom := by
    rw [hφj, hχ]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc]
    rw [reassoc_of% (baseChangeFactorIso_assoc B S hS (hpN e) (hiUn e) (hpNU j) (hpNU i)
      T.obj.left), reassoc_of% hθ']
    rw [reassoc_of% (baseChangeSquareIso_paste B S hS (hpN e) (hiWn e) (hpNW i) (hpNW j)
      (hpM e) Bi)]
    simp
  -- the glueing datum at the stage `j` and its preimage there
  have hequiv := isEquivalence_glueingFunctor_of_compl_singleton B S hS (hsqW j) hUopen
    (hWopen j) hU (hW j)
  obtain ⟨X, ⟨Ξ⟩⟩ := Functor.EssSurj.mem_essImage (F := glueingFunctor B S hS (hsqW j).w)
    (⟨⟨T.obj.left, (baseChange B S hS (W.map e)).obj Bi, φj.hom⟩, inferInstance⟩ :
      IsoComma (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j)))
  refine ⟨X, ⟨ObjectProperty.isoMk _ (Comma.isoMk
    ((IsoComma.fst (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j))).mapIso Ξ)
    (Iso.app (coneIso B S hS M W pM j) X ≪≫
      (baseChange B S hS (pM j)).mapIso
        ((IsoComma.snd (baseChange B S hS (iUn j)) (baseChange B S hS (iWn j))).mapIso Ξ) ≪≫ χ)
    ?_)⟩⟩
  simp only [Functor.mapIso_hom]
  exact squareCondition_of_stage B S hS hsq.w (hsqW j).w (hpNU j) (hpNW j)
    (Over.mkIdTerminal.hom_ext _ _) hrel Ξ.hom.hom.w

include hsq hsqW hpNU hpNW hiUn hiWn hloc hoverlap hUopen hWopen hU hW in
/-- **The algebraic spaces of finite presentation over the base are the `2`-fibre product
`FP_U ×_{FP_N} FP_M`, when `M` is a cofiltered limit of open neighbourhoods of the point
complementary to `U` and `N` is the corresponding limit of their intersections with `U`.**

This is Stacks 0E90 for `M = Spec O_{S,s}` and `N = Spec O_{S,s} ∖ {s}`, granted the two
colimit identifications carried as the hypotheses `hloc` and `hoverlap`: what the theorem proves
is the formal combination, namely that the comparison functor is faithful, full and essentially
surjective. Faithfulness and fullness come from the equivalence of Stacks 0E8Z at a single
neighbourhood, which applies because the complement of the point and any neighbourhood of it
cover the base; essential surjectivity needs in addition that a glueing datum descends to a
neighbourhood. -/
@[stacks 0E90 "the equivalence, granted the two colimit identifications. The theorem is stated \
for an arbitrary object `M` of the site equipped with a cofiltered system of open neighbourhoods \
`W i` of the point complementary to `U`, and an object `N` over their intersections with `U`, \
such that base change exhibits `FP_M` as the cofiltered 2-colimit of the `FP_{W i}` and `FP_N` \
as that of the `FP_{W i ∩ U}`; these two statements are the hypotheses `hloc` and `hoverlap`. \
For `M = Spec O_{S,s}` they are what Stacks 07SK gives once the affine open neighbourhoods of \
`s` are known to have `Spec O_{S,s}` as their limit and the `W i ∩ U` to have its puncture as \
theirs — neither limit identification is available in this library, which is why the two \
colimit statements are carried as hypotheses rather than proved"]
theorem isEquivalence_glueingFunctor_of_colimit :
    (glueingFunctor B S hS hsq.w).IsEquivalence := by
  have hfaithful := faithful_glueingFunctor_of_colimit B S hS hsq hsqW hloc
    hUopen hWopen hU hW
  have hfull := full_glueingFunctor_of_colimit B S hS hsq hsqW hpNU hpNW
    hiUn hiWn hloc hoverlap hUopen hWopen hU hW
  have hessSurj := essSurj_glueingFunctor_of_colimit B S hS hsq hsqW hpNU
    hpNW hiUn hiWn hloc hoverlap hUopen hWopen hU hW
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Limit

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
