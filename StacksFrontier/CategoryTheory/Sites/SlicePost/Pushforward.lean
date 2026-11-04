module

public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The localized pushforward square `f'_* j_U^{-1} = j_V^{-1} f_*`

Let `u : C ⥤ D` be a continuous functor of sites `(C, J)`, `(D, K)`, let `V : C` and put
`U = u.obj V`.  Stacks 03CF attaches to this data the localized morphism of sites
`f' : D/U → C/V`, given by the continuous functor `u' = Over.post u : Over V ⥤ Over U`, and its
last assertion is the identity

```
  f'_* ∘ j_U^{-1} = j_V^{-1} ∘ f_* .
```

(Stacks writes `u : D → C` for the continuous functor, so Stacks' `C` is this file's `D` and
Stacks' `D` is this file's `C`; Stacks' `V ∈ Ob(D)` is this file's `V : C` and Stacks' `U = u(V)`
is `u.obj V`.  Stacks 03EF repeats the same identity as its own last sentence.)

Stacks proves it by the computation
`(j_V^{-1} f_* F)(V'/V) = f_* F(V') = F(u(V')) = (j_U^{-1}F)(u(V')/U) = (f'_* j_U^{-1} F)(V'/V)`,
noting that it "holds even for presheaves".  In Mathlib all four functors are
`Functor.sheafPushforwardContinuous`, i.e. precomposition with an opposite functor, and the
computation is exactly the equality of functors

```
  Over.post u ⋙ Over.forget U = Over.forget V ⋙ u
```

which is `Over.post_forget_eq_forget_comp` and holds by `rfl`.  So the identity is a strict
equality of functors on `A`-valued sheaves for *any* target category `A`
(`sheafPushforwardContinuous_overPost_eq`), and the proof is `rfl` as well.  This is the same
mechanism as `inverseImage_eq` in
`StacksFrontier/CategoryTheory/Sites/Localization/RelocalizationTriangle.lean`.

Passing to left adjoints turns the equality into the corresponding statement about the lower
shrieks and the inverse image,

```
  (f')^{-1} ∘ j_{U!} ≅ j_{V!} ∘ f^{-1} ,
```

which is `sheafPullbackOverPostIso`.  It is an isomorphism rather than an equality because
`Functor.sheafPullback` is a *chosen* left adjoint; uniqueness of left adjoints
(`Adjunction.leftAdjointUniq`) supplies the comparison.  This is the third displayed equality in
the proof of Stacks 03CF (`j_{U!}(f')^{-1}H = f^{-1}j_{V!}H`), reached here without Stacks 00WY.

## What is *not* here

Stacks 03CF has three further assertions, none of which follows from the above:

* that `f'` is a *morphism of sites*, i.e. that `(f')^{-1}` is exact.  This clause (a) is now
  proved in the generality of 03CF, through Stacks 00Y1 as Stacks does, by
  `Functor.isMorphismOfSites_overPost_of_isMorphismOfSites` in
  `StacksFrontier/CategoryTheory/Sites/SlicePost/MorphismOfSitesGeneral.lean`; it does not go
  through the description of `(f')^{-1}` (clause (c)), only through the explicit description of the
  *objects* of `Sh(C/U)`.  Under the stronger hypotheses of Stacks 03EF it is also available
  directly, as `Functor.isMorphismOfSites_overPost` in
  `StacksFrontier/CategoryTheory/Sites/SlicePost/MorphismOfSites.lean`.
* that the square of *topoi* commutes, i.e. `(f')^{-1} ∘ j_V^{-1} = j_U^{-1} ∘ f^{-1}`.  This is a
  different square from the one proved here — it pairs two inverse images, whereas
  `sheafPushforwardContinuous_overPost_eq` pairs a pushforward with an inverse image — and Stacks
  obtains it at the very end of the proof from the description of `(f')^{-1}` plus Stacks 03EE.
* the description of `(f')^{-1}` under the identifications of Stacks 00Y1.  This is clause (c).
  It is *not* circular, contrary to an earlier note here: see
  `StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean`, where it is proved.  Stacks does
  derive exactness of `(f')^{-1}` from (c), but the obligation reduces via
  `Over.comp_hom_of_terminal` to a single equation at the terminal object, and under 03EF's
  hypotheses the ingredient that equation needs is available independently of (c).

## Main results

* `CategoryTheory.sheafPushforwardContinuous_overPost_eq`: `f'_* j_U^{-1} = j_V^{-1} f_*`.
* `CategoryTheory.sheafPullbackOverPostIso`: `(f')^{-1} j_{U!} ≅ j_{V!} f^{-1}`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

universe v u v' u'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (u : C ⥤ D) [u.IsContinuous J K] (V : C)
  [(Over.post (X := V) u).IsContinuous (J.over V) (K.over (u.obj V))] (A : Type*) [Category A]

/-- **Stacks 03CF, last assertion**: `f'_* j_U^{-1} = j_V^{-1} f_*`, as a strict equality of
functors `Sheaf K A ⥤ Sheaf (J.over V) A` for an arbitrary target category `A`.

In Lean's left-to-right composition order the left-hand side below is `f'_* ∘ j_U^{-1}` and the
right-hand side is `j_V^{-1} ∘ f_*`.  Both are precomposition with the opposite of a functor
`Over V ⥤ D`, and the two functors agree on the nose by `Over.post_forget_eq_forget_comp`; this is
Stacks' remark that the identity "holds even for presheaves".

Clause (a) of Stacks 03CF, that `f'` is a morphism of sites, is
`Functor.isMorphismOfSites_overPost_of_isMorphismOfSites` in
`StacksFrontier/CategoryTheory/Sites/SlicePost/MorphismOfSitesGeneral.lean`, in the generality of
03CF.  Clauses (b) and (c) are proved in
`StacksFrontier/CategoryTheory/Sites/SliceTopos/InverseImage.lean`, also in 03CF's own generality. -/
@[stacks 03CF "Clause (d): the identity `f'_* j_U^{-1} = j_V^{-1} f_*`, for sheaves valued in any
  category; also the last sentence of 03EF. Clause (a) is in
  Sites/SlicePost/MorphismOfSitesGeneral.lean and clauses (b) and (c) are in
  Sites/SliceTopos/InverseImage.lean, all three in 03CF's own generality."]
theorem sheafPushforwardContinuous_overPost_eq :
    (Over.forget (u.obj V)).sheafPushforwardContinuous A (K.over (u.obj V)) K ⋙
        (Over.post (X := V) u).sheafPushforwardContinuous A (J.over V) (K.over (u.obj V)) =
      u.sheafPushforwardContinuous A J K ⋙
        (Over.forget V).sheafPushforwardContinuous A (J.over V) J :=
  rfl

variable [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [((Over.forget V).sheafPushforwardContinuous A (J.over V) J).IsRightAdjoint]
  [((Over.forget (u.obj V)).sheafPushforwardContinuous A (K.over (u.obj V)) K).IsRightAdjoint]
  [((Over.post (X := V) u).sheafPushforwardContinuous A (J.over V)
        (K.over (u.obj V))).IsRightAdjoint]

/-- **The lower-shriek form of Stacks 03CF's computation**: `(f')^{-1} j_{U!} ≅ j_{V!} f^{-1}`.

This is the isomorphism `j_{U!}(f')^{-1}H ≅ f^{-1}j_{V!}H` displayed in the proof of Stacks 03CF,
obtained here not from Stacks 00WY but by taking left adjoints in
`sheafPushforwardContinuous_overPost_eq`: `(f')^{-1} ⋙ j_{U!}` is left adjoint to
`j_U^{-1} ⋙ f'_*` and `j_{V!} ⋙ f^{-1}` is left adjoint to `f_* ⋙ j_V^{-1}`, and those two right
adjoints are equal.  Uniqueness of left adjoints does the rest. -/
@[stacks 03CF "The isomorphism `j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` of the proof of 03CF, deduced from
  clause (d) by uniqueness of left adjoints. As in the clause note on
  `sheafPushforwardContinuous_overPost_eq`, clauses (b) and (c) of 03CF are not covered; they
  are in Sites/SliceTopos/InverseImage.lean."]
noncomputable def sheafPullbackOverPostIso :
    (Over.post (X := V) u).sheafPullback A (J.over V) (K.over (u.obj V)) ⋙
        (Over.forget (u.obj V)).sheafPullback A (K.over (u.obj V)) K ≅
      (Over.forget V).sheafPullback A (J.over V) J ⋙ u.sheafPullback A J K :=
  -- `adjPost : (f')^{-1} ⊣ f'_*`, `adjForgetU : j_{U!} ⊣ j_U^{-1}`, and their composite is left
  -- adjoint to `j_U^{-1} ⋙ f'_*`.
  letI adjPost := (Over.post (X := V) u).sheafAdjunctionContinuous A (J.over V) (K.over (u.obj V))
  letI adjForgetU := (Over.forget (u.obj V)).sheafAdjunctionContinuous A (K.over (u.obj V)) K
  -- `adjForgetV : j_{V!} ⊣ j_V^{-1}`, `adjU : f^{-1} ⊣ f_*`, and their composite is left adjoint
  -- to `f_* ⋙ j_V^{-1}`, which by clause (d) is the same functor.
  letI adjForgetV := (Over.forget V).sheafAdjunctionContinuous A (J.over V) J
  letI adjU := u.sheafAdjunctionContinuous A J K
  Adjunction.leftAdjointUniq (adjPost.comp adjForgetU)
    ((sheafPushforwardContinuous_overPost_eq J K u V A).symm ▸ adjForgetV.comp adjU)

end CategoryTheory
