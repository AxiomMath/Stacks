module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The composition coherence of `restrictFunctorIsoPullback`

Mathlib's `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies the
restriction functor along an open immersion `f : X ⟶ Y` with the pullback functor along `f`.  It
is defined as `CategoryTheory.Adjunction.leftAdjointUniq`, the comparison of two left adjoints of
`AlgebraicGeometry.Scheme.Modules.pushforward f`, and Mathlib proves no coherence for it at all:
nothing relates it to the two composition isomorphisms
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, so an iterated restriction cannot be compared
with an iterated pullback.

This file supplies that coherence.  For open immersions `f : X ⟶ Y` and `g : Y ⟶ Z` the square

```
restrictFunctor (f ≫ g)  ---------------------->  pullback (f ≫ g)
        |                                                 ^
        | restrictFunctorComp f g                         | pullbackComp f g
        v                                                 |
restrictFunctor g ⋙ restrictFunctor f  ------->  pullback g ⋙ pullback f
```

commutes, the horizontal arrows being `restrictFunctorIsoPullback` and its whiskerings.

## Implementation notes

`restrictFunctorIsoPullback` is a `leftAdjointUniq`, so it is pinned down by *uniqueness of the
left-adjoint comparison*: `CategoryTheory.conjugateEquiv` is a bijection between natural
transformations `pullback f ⟶ restrictFunctor f` and natural transformations
`pushforward f ⟶ pushforward f`, and the comparison is the transformation whose conjugate is the
identity (`conjugateEquiv_restrictFunctorIsoPullback_inv`).  Conjugation turns composition into
composition (`CategoryTheory.conjugateEquiv_comp`) and whiskering into whiskering
(`CategoryTheory.conjugateEquiv_whiskerLeft`, `CategoryTheory.conjugateEquiv_whiskerRight`), so
the whole square is proved once its four links are conjugated.  Three of the four conjugates are
already available: two are the identity by the lemma just quoted, and the pullback link is
Mathlib's `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`.

The one genuinely new input is `conjugateEquiv_restrictFunctorComp_inv`, the conjugate of the
restriction composition isomorphism.  It is tractable because the pushforward side of all of
these adjunctions is the identity on sections — this is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app` — so the conjugate becomes a
composite of four restriction maps of one presheaf which returns to the open it started from,
and the category of opens is thin (`presheaf_map_comp₄_eq_id`).

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.conjugateEquiv_restrictFunctorIsoPullback_inv`: the
  conjugate of `restrictFunctorIsoPullback` is the identity of `pushforward`.  This is the
  defining property of the comparison.
* `Stacks.AlgebraicGeometry.ModuleLimits.conjugateEquiv_restrictFunctorComp_inv`: the conjugate
  of `restrictFunctorComp` is `pushforwardComp`.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp` and
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_inv_comp`: **the coherence**,
  in the two directions.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_app_comp`: the coherence
  at a single module.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq`: the coherence
  with the `restrictFunctorCongr`/`pullbackCongr` reindexing carried out.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-! ### Thinness of the category of opens -/

/-- A four-fold composite of restriction maps of one presheaf of modules which returns to the open
it started from is the identity, because the category of opens of a scheme is thin. -/
theorem presheaf_map_comp₄_eq_id {W : Scheme.{u}} (M : W.Modules) {A B C D : W.Opens}
    (p : op A ⟶ op B) (q : op B ⟶ op C) (r : op C ⟶ op D) (s : op D ⟶ op A) :
    M.presheaf.map p ≫ M.presheaf.map q ≫ M.presheaf.map r ≫ M.presheaf.map s = 𝟙 _ := by
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp,
    Subsingleton.elim (p ≫ q ≫ r ≫ s) (𝟙 _), M.presheaf.map_id]

/-! ### The conjugates of the three comparison isomorphisms -/

/-- **`restrictFunctorIsoPullback` is the left-adjoint comparison**, i.e. its conjugate relative
to the restriction adjunction and the pullback–pushforward adjunction is the identity of
`pushforward f`.

This is the defining property of `CategoryTheory.Adjunction.leftAdjointUniq`, and the restriction
analogue of Mathlib's `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom`. -/
theorem conjugateEquiv_restrictFunctorIsoPullback_inv :
    conjugateEquiv (restrictAdjunction f) (pullbackPushforwardAdjunction f)
      (restrictFunctorIsoPullback f).inv = 𝟙 (pushforward f) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

/-- **The conjugate of the restriction composition isomorphism is the pushforward composition
isomorphism.**  This is the restriction analogue of Mathlib's
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, which Mathlib proves for
`pullback` and not for `restrictFunctor`.

It is the only computation in this file.  All four factors of the conjugate are restriction maps
of the presheaf of the module being pushed forward — the two halves of the unit of the composite
restriction adjunction, the composition isomorphism itself, and the counit of the restriction
adjunction for `f ≫ g` — and they return to the open they started from, so
`presheaf_map_comp₄_eq_id` finishes. -/
theorem conjugateEquiv_restrictFunctorComp_inv :
    conjugateEquiv (restrictAdjunction (f ≫ g))
      ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictFunctorComp f g).inv = (pushforwardComp f g).inv := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp only [pushforward_obj_obj, Scheme.Hom.comp_base, Opens.map_comp_obj, Functor.comp_obj,
    conjugateEquiv_apply_app, Adjunction.comp_unit_app, Functor.comp_map, Category.assoc,
    Hom.comp_app, restrictAdjunction_unit_app_app, homOfLE_leOfHom,
    pushforward_obj_presheaf_map, Opens.map_comp_map, Opens.map_homOfLE, pushforward_map_app,
    restrictFunctorComp_inv_app_app, Functor.op_obj, eqToHom_op,
    restrictAdjunction_counit_app_app, pushforwardComp_inv_app_app]
  exact presheaf_map_comp₄_eq_id M _ _ _ _

/-! ### The coherence -/

/-- **The composition coherence of `restrictFunctorIsoPullback`, inverse direction.**  Identifying
the pullback along `f ≫ g` with the restriction along `f ≫ g` is the same as identifying it with
the iterated pullback, then identifying each factor with a restriction, then collapsing the
iterated restriction.

Each of the four links is conjugated separately — by
`conjugateEquiv_restrictFunctorComp_inv`, by `CategoryTheory.conjugateEquiv_whiskerRight` and
`CategoryTheory.conjugateEquiv_whiskerLeft` together with
`conjugateEquiv_restrictFunctorIsoPullback_inv`, and by Mathlib's
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` — and the four conjugates
compose to the identity, which is the conjugate of the left-hand side. -/
theorem restrictFunctorIsoPullback_inv_comp :
    (restrictFunctorIsoPullback (f ≫ g)).inv =
      (pullbackComp f g).inv ≫
        Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).inv ≫
          Functor.whiskerRight (restrictFunctorIsoPullback g).inv (restrictFunctor f) ≫
            (restrictFunctorComp f g).inv := by
  refine (conjugateEquiv (restrictAdjunction (f ≫ g))
    (pullbackPushforwardAdjunction (f ≫ g))).injective ?_
  rw [conjugateEquiv_restrictFunctorIsoPullback_inv,
    ← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)) _,
    ← conjugateEquiv_comp _ ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f)) _,
    ← conjugateEquiv_comp _ ((restrictAdjunction g).comp (restrictAdjunction f)) _,
    conjugateEquiv_restrictFunctorComp_inv,
    conjugateEquiv_whiskerRight (restrictAdjunction g) (pullbackPushforwardAdjunction g)
      (restrictAdjunction f),
    conjugateEquiv_whiskerLeft (restrictAdjunction f) (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction g),
    conjugateEquiv_restrictFunctorIsoPullback_inv,
    conjugateEquiv_restrictFunctorIsoPullback_inv,
    conjugateEquiv_pullbackComp_inv]
  simp

/-- **The composition coherence of `restrictFunctorIsoPullback`.**  Collapsing an iterated
restriction and then identifying it with the pullback along the composite is the same as
identifying each restriction with a pullback and then collapsing the iterated pullback.

This is `restrictFunctorIsoPullback_inv_comp` read on the other side of the isomorphisms. -/
theorem restrictFunctorIsoPullback_hom_comp :
    (restrictFunctorIsoPullback (f ≫ g)).hom =
      (restrictFunctorComp f g).hom ≫
        Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
          Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom ≫
            (pullbackComp f g).hom :=
  (Iso.inv_eq_inv (restrictFunctorIsoPullback (f ≫ g))
    (restrictFunctorComp f g ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback g) (restrictFunctor f) ≪≫
        Functor.isoWhiskerLeft (pullback g) (restrictFunctorIsoPullback f) ≪≫
          pullbackComp f g)).mp (restrictFunctorIsoPullback_inv_comp f g)

/-- The composition coherence of `restrictFunctorIsoPullback` at a single module. -/
theorem restrictFunctorIsoPullback_hom_app_comp (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback g).hom.app M) ≫
          (restrictFunctorIsoPullback f).hom.app ((pullback g).obj M) ≫
            (pullbackComp f g).hom.app M := by
  have := NatTrans.congr_app (restrictFunctorIsoPullback_hom_comp f g) M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using this

/-- The composition coherence of `restrictFunctorIsoPullback` at a single module, inverse
direction. -/
theorem restrictFunctorIsoPullback_inv_app_comp (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).inv.app M =
      (pullbackComp f g).inv.app M ≫
        (restrictFunctorIsoPullback f).inv.app ((pullback g).obj M) ≫
          (restrictFunctor f).map ((restrictFunctorIsoPullback g).inv.app M) ≫
            (restrictFunctorComp f g).inv.app M := by
  have := NatTrans.congr_app (restrictFunctorIsoPullback_inv_comp f g) M
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using this

/-! ### The coherence along an equality of open immersions

When the composite `f ≫ g` is an open immersion `k` presented differently — `X.homOfLE e ≫ W.ι`
presented as `V.ι`, say — the comparison is `restrictFunctorComp` followed by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`.  The two lemmas below carry that
reindexing across the coherence.
-/

/-- `restrictFunctorCongr` along the trivial equality is the identity. -/
theorem restrictFunctorCongr_rfl (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctorCongr (rfl : f = f)).hom = 𝟙 _ := by
  refine NatTrans.ext (funext fun M => Scheme.Modules.hom_ext _ _ fun U => ?_)
  simp
  rfl

/-- `restrictFunctorIsoPullback` is compatible with reindexing along an equality of open
immersions: `restrictFunctorCongr` on the restriction side matches
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` on the pullback side. -/
theorem restrictFunctorCongr_hom_restrictFunctorIsoPullback_hom {f f' : X ⟶ Y}
    [i : IsOpenImmersion f] [i' : IsOpenImmersion f'] (h : f = f') :
    (restrictFunctorCongr h).hom ≫ (restrictFunctorIsoPullback f').hom =
      (restrictFunctorIsoPullback f).hom ≫ (pullbackCongr h).hom := by
  subst h
  obtain rfl : i = i' := rfl
  rw [restrictFunctorCongr_rfl]
  simp [pullbackCongr]

/-- **The composition coherence with the reindexing carried out.**  For open immersions `f`, `g`
and an open immersion `k` with `f ≫ g = k`, the comparison between the iterated restriction and
the restriction along `k` matches the comparison between the iterated pullback and the pullback
along `k`.

With `f := X.homOfLE e`, `g := W.ι` and `k := V.ι` the left-hand side is the comparison between
restricting to `W` and then to `V ≤ W` and restricting to `V` directly. -/
theorem restrictFunctorIsoPullback_hom_comp_of_eq {k : X ⟶ Z} [IsOpenImmersion k]
    (h : f ≫ g = k) :
    (restrictFunctorComp f g).inv ≫ (restrictFunctorCongr h).hom ≫
        (restrictFunctorIsoPullback k).hom =
      Functor.whiskerRight (restrictFunctorIsoPullback g).hom (restrictFunctor f) ≫
        Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom ≫
          (pullbackComp f g).hom ≫ (pullbackCongr h).hom := by
  rw [restrictFunctorCongr_hom_restrictFunctorIsoPullback_hom,
    restrictFunctorIsoPullback_hom_comp]
  simp

end Stacks.AlgebraicGeometry.ModuleLimits
