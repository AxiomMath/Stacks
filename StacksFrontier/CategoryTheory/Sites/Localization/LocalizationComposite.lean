module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp

/-! # Localizing a cocontinuous functor

Let `u : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`, let `U` be an
object of `C` and put `V = u(U)`.  Stacks 03EG localizes `u` at `U`: the induced functor

```
  u' = Over.post u : C/U ⥤ D/V,    (U'/U) ↦ (u(U')/V)
```

sits in a square with the two localization functors `j_U = Over.forget U : C/U ⥤ C` and
`j_V = Over.forget V : D/V ⥤ D`,

```
  C/U --j_U--> C
   | u'         | u
   v            v
  D/V --j_V--> D
```

and the content of the lemma is that this square commutes, that `u'` is again cocontinuous for the
localized topologies `J.over U` and `K.over V`, and that consequently the induced square of topoi

```
  Sh(C/U) --j_U--> Sh(C)
   | f'             | f
   v                v
  Sh(D/V) --j_V--> Sh(D)
```

commutes, where `f` and `f'` are the morphisms of topoi attached to `u` and to `u'` by Stacks 00XO.

## What the source's proof does, and what Lean needs

Commutativity of the square of categories is Stacks' "clear": in Lean it is an equality of
functors that holds by `rfl` (`Over.post_forget_eq_forget_comp`).

The one piece of mathematics is that `u'` is cocontinuous.  Stacks argues it directly: given
`U'/U` in `C/U` and a covering `{V_j/V → u(U')/V}` of `u(U')/V` in `D/V`, cocontinuity of `u`
supplies a covering `{U'_i → U'}` in `C` together with `α : I → J` and morphisms
`φ_i : u(U'_i) → V_{α(i)}` over `U'`; viewing each `U'_i` over `U` through `U'_i → U' → U`, the
family `{U'_i/U → U'/U}` is a covering in `C/U` and *the same* `α` and `φ_i` exhibit
`{u(U'_i)/V → u(U')/V}` as a refinement of `{V_j/V → u(U')/V}`.  That is, the refinement data
transfers verbatim; only the bookkeeping of the structure maps to `U` and `V` changes.

Mathlib already carries out exactly this argument, in the sieve-theoretic formulation of
cocontinuity: `CategoryTheory.GrothendieckTopology.instIsCocontinuousOverObjPostOver` states that
`Over.post u` is cocontinuous for `J.over U` and `K.over (u.obj U)`, its proof being the transport
`Sieve.overEquiv_functorPullback_post` of a sieve on `u(U')/V` to a sieve on `u(U')` followed by
`u.cover_lift`.  So `isCocontinuous_overPost` below is a citation of Mathlib rather than a new
proof.

Given cocontinuity of `u'`, the square of topoi commutes because the square of functors commutes
on the nose and the direct image of a composite of cocontinuous functors is the composite of the
direct images, which is Stacks 03L5 (`sheafPushforwardCocontinuousCompIso`, in
`StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp`).

## Main results

* `overPost_comp_forget` (Stacks 03EG): the square of categories commutes,
  `u' ⋙ j_V = j_U ⋙ u`.
* `isCocontinuous_overPost` (Stacks 03EG): `u'` is cocontinuous for the localized topologies.
* `sheafPushforwardCocontinuousOverPostIso` (Stacks 03EG): the square of topoi commutes,
  `f'_* ⋙ j_{V*} ≅ j_{U*} ⋙ f_*`.

## Implementation notes

The square of topoi is recorded through its direct images.  `Functor.sheafPushforwardCocontinuous`
is by definition the functor `gStar` of
`StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousAdjunction`, so the four functors
appearing in `sheafPushforwardCocontinuousOverPostIso` are literally `f_*`, `f'_*`, `j_{U*}` and
`j_{V*}` for the morphisms of topoi of Stacks 00XO.  Since a morphism of topoi is determined by
its direct image (the inverse image being its left adjoint), commutativity of the direct images is
commutativity of the square of topoi; the corresponding statement for the inverse images follows by
uniqueness of left adjoints and is not restated.  This matches the way Stacks 03L5 is recorded in
`CocontinuousComp`, where only the direct image of a composite is treated.

Note that the *strong*, Beck–Chevalley form `f'_* ∘ j_U^{-1} = j_V^{-1} ∘ f_*` is deliberately not
claimed: the section context of Stacks 03EG points out that, unlike in the situation of Stacks
03CF, that identity does not hold here.  The continuous counterpart, where it does hold, is
`StacksFrontier.CategoryTheory.Sites.SlicePost.Pushforward`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) [u.IsCocontinuous J K] (U : C)

/-- **Stacks 03EG**, the square of categories.  With `V = u(U)`, the localized functor
`u' = Over.post u : C/U ⥤ D/V` and the localization functors `j_U = Over.forget U` and
`j_V = Over.forget V` form a commutative square, `u' ⋙ j_V = j_U ⋙ u`.  Stacks calls this
"clear"; in Lean the two composites are equal by `rfl`. -/
@[stacks 03EG "the square of categories commutes: `u' ⋙ j_V = j_U ⋙ u`"]
theorem overPost_comp_forget :
    (Over.post u : Over U ⥤ Over (u.obj U)) ⋙ Over.forget (u.obj U) = Over.forget U ⋙ u :=
  Over.post_forget_eq_forget_comp u U

/-- **Stacks 03EG**, the mathematical content.  If `u : C ⥤ D` is cocontinuous then so is the
localized functor `u' = Over.post u : C/U ⥤ D/u(U)`, for the localized topologies `J.over U` and
`K.over (u.obj U)`.

Stacks proves this by transferring refinement data verbatim: a covering of `u(U')/u(U)` in
`D/u(U)` is in particular a covering of `u(U')` in `D`, cocontinuity of `u` refines its
`u`-image by a covering `{U'_i → U'}` of `C`, and the very same index map and comparison
morphisms exhibit the refinement after every object is viewed over `U`, resp. over `u(U)`.  In
Mathlib's sieve-theoretic formulation this is
`CategoryTheory.GrothendieckTopology.instIsCocontinuousOverObjPostOver`. -/
@[stacks 03EG "the left vertical arrow `u'` is cocontinuous"]
theorem isCocontinuous_overPost :
    (Over.post u : Over U ⥤ Over (u.obj U)).IsCocontinuous (J.over U) (K.over (u.obj U)) :=
  inferInstance

/-- **Stacks 03EG**, the square of topoi.  Let `f : Sh(C) ⟶ Sh(D)` and
`f' : Sh(C/U) ⟶ Sh(D/u(U))` be the morphisms of topoi attached to `u` and to
`u' = Over.post u` by Stacks 00XO, and let `j_U : Sh(C/U) ⟶ Sh(C)` and
`j_V : Sh(D/u(U)) ⟶ Sh(D)` be those attached to the localization functors.  Then the square of
topoi commutes: there is a natural isomorphism `f'_* ⋙ j_{V*} ≅ j_{U*} ⋙ f_*` of functors
`Sh(C/U) ⥤ Sh(D)`.

Both composites compute the direct image of one and the same functor `C/U ⥤ D`, since
`u' ⋙ j_V = j_U ⋙ u` by `overPost_comp_forget`; the isomorphism is therefore obtained by
comparing each side with that direct image using Stacks 03L5. -/
@[stacks 03EG "the square of topoi commutes: `f'_* ⋙ j_{V*} ≅ j_{U*} ⋙ f_*`"]
noncomputable def sheafPushforwardCocontinuousOverPostIso :
    (Over.post u : Over U ⥤ Over (u.obj U)).sheafPushforwardCocontinuous (Type u)
          (J.over U) (K.over (u.obj U)) ⋙
        (Over.forget (u.obj U)).sheafPushforwardCocontinuous (Type u) (K.over (u.obj U)) K ≅
      (Over.forget U).sheafPushforwardCocontinuous (Type u) (J.over U) J ⋙
        u.sheafPushforwardCocontinuous (Type u) J K :=
  (sheafPushforwardCocontinuousCompIso (J.over U) (K.over (u.obj U)) K
        (Over.post u) (Over.forget (u.obj U))).symm.trans
    (sheafPushforwardCocontinuousCompIso (J.over U) J K (Over.forget U) u)
