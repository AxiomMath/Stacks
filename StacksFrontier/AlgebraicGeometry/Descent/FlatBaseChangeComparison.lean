module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeCoherent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange

/-!
# The inverse-image description of the base-change morphism

For a commutative square of schemes
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
the comparison morphism `g^* f_* ⟶ f'_* (g')^*` is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, defined as the mate of the
identification `g'_* f_* ≅ f'_* g_*` of the two composite *direct* images, with respect to the
adjunctions attached to the *vertical* maps `g'` and `g`.

It has a second standard description: it is also the mate of the identification
`g^* (f')^* ≅ f^* (g')^*` of the two composite *inverse* images,
`Stacks.Modules.pullbackTwoSquare`, with respect to the adjunctions attached to the *horizontal*
maps `f` and `f'`.  That is `Stacks.Modules.baseChangeNatTrans_eq_mateEquiv`, and it is what
this file proves; everything after it is the resulting API, which is the one actually used to
compute with the morphism, since it expresses the morphism through the adjunctions of `f` and
`f'` rather than of `g` and `g'`.

## Main results

* `Stacks.Modules.conjugateEquiv_pullbackSquareIso_hom`: the direct-image square isomorphism is
  the conjugate of the inverse-image square isomorphism.  This is the whole content; the rest is
  formal.
* `Stacks.Modules.baseChangeNatTrans_eq_mateEquiv`: the base-change morphism is the mate of
  `Stacks.Modules.pullbackTwoSquare` along the horizontal adjunctions.
* `Stacks.Modules.baseChangeNatTrans_app` computes the base-change morphism as the adjoint
  transpose of `(g')^*` applied to the counit of `f^* ⊣ f_*`.
* `Stacks.Modules.homEquiv_pullbackSquareIso_comp` says the same thing in terms of
  `CategoryTheory.Adjunction.homEquiv`: the base-change morphism *is* that transpose, and
  `Stacks.Modules.eq_baseChangeNatTrans_app` says it is the only morphism that is.
* `Stacks.Modules.pullback_map_baseChangeNatTrans_app_comp_counit` and
  `Stacks.Modules.map_unit_comp_baseChangeNatTrans_app` are the two triangle identities relating
  the base-change morphism to the units and counits of the two horizontal adjunctions.
* `Stacks.Modules.selfBaseChange_eq`: the self-base-change morphism of a morphism `f`, used in
  Tag 07TT, is a value of the base-change morphism.

## Implementation notes

The proof of `Stacks.Modules.baseChangeNatTrans_eq_mateEquiv` is
`CategoryTheory.iterated_mateEquiv_conjugateEquiv`: taking the mate of a 2-cell first
horizontally and then vertically gives the conjugate of the original 2-cell.  Applying it to the
inverse-image square turns the horizontal mate into the vertical one, *provided* the two square
isomorphisms are conjugate, which is
`Stacks.Modules.conjugateEquiv_pullbackSquareIso_hom`.  That in turn is
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` applied to the two
decompositions, together with the corresponding statement for the `Congr` isomorphisms.

The two descriptions are provably but not definitionally equal, so each statement below about
`baseChangeNatTrans` phrased through the horizontal adjunctions goes through
`Stacks.Modules.baseChangeNatTrans_eq_mateEquiv` rather than through `rfl`.

## References

* [Stacks Project, Tag 02KF](https://stacks.math.columbia.edu/tag/02KF)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Modules

variable {X Y Z : Scheme.{u}}

/-- `AlgebraicGeometry.Scheme.Modules.pullbackCongr` at a reflexivity proof is the identity. -/
lemma pullbackCongr_rfl (a : X ⟶ Y) :
    Scheme.Modules.pullbackCongr (rfl : a = a) = Iso.refl _ := rfl

/-- `AlgebraicGeometry.Scheme.Modules.pushforwardCongr` at a reflexivity proof is the
identity. -/
lemma pushforwardCongr_rfl (a : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : a = a) = Iso.refl _ := by
  ext M U; simp

/-- The direct-image comparison attached to an equality of morphisms is the conjugate of the
inverse-image comparison attached to the same equality. -/
lemma conjugateEquiv_pullbackCongr_hom {a b : X ⟶ Y} (h : a = b) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
        (Scheme.Modules.pullbackPushforwardAdjunction b)
        (Scheme.Modules.pullbackCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).hom := by
  subst h
  rw [pullbackCongr_rfl, pushforwardCongr_rfl]
  simp

section Bridge

variable {X' S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ Y} {g : S' ⟶ Y}

/-- The identification of the two composite direct images around a commutative square is the
conjugate of the identification of the two composite inverse images.  This is the mathematical
content of the comparison of the two base-change constructions. -/
lemma conjugateEquiv_pullbackSquareIso_hom (w : g' ≫ f = f' ≫ g) :
    conjugateEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction g'))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f'))
        (pullbackTwoSquare f f' g g' w) =
      (Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w).hom := by
  rw [Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso]
  change conjugateEquiv _ _
      ((Scheme.Modules.pullbackComp f' g).hom ≫
        (Scheme.Modules.pullbackCongr w.symm).hom ≫
        (Scheme.Modules.pullbackComp g' f).inv) = _
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv g' f,
      ← conjugateEquiv_pullbackCongr_hom w,
      ← Stacks.ModuleSkyscraper.conjugateEquiv_pullbackComp_hom f' g,
      conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc]

/-- **The inverse-image description of the base-change morphism.**  The base-change morphism,
defined as the mate of the direct-image square isomorphism along the vertical adjunctions, is
also the mate of the inverse-image square isomorphism along the horizontal adjunctions. -/
theorem baseChangeNatTrans_eq_mateEquiv (w : g' ≫ f = f' ≫ g) :
    Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w =
      (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f')
        (pullbackTwoSquare f f' g g' w)) := by
  have key := iterated_mateEquiv_conjugateEquiv
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f')
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction g')
      (pullbackTwoSquare f f' g g' w)
  rw [conjugateEquiv_pullbackSquareIso_hom w] at key
  rw [Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans_eq, ← key]
  exact (mateEquiv _ _).symm_apply_apply _

/-- The base-change morphism at a module `M` on `X`, written out: it is the unit of
`(f')^* ⊣ (f')_*` followed by `(f')_*` applied to the composite of the pullback comparison
isomorphism with `(g')^*` of the counit of `f^* ⊣ f_*`. -/
theorem baseChangeNatTrans_app (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M =
      (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M)) ≫
        (Scheme.Modules.pushforward f').map
          ((pullbackSquareIso f f' g g' w).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
            (Scheme.Modules.pullback g').map
              ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) := by
  rw [baseChangeNatTrans_eq_mateEquiv]
  simp [pullbackTwoSquare, Functor.map_comp]

/-- The base-change morphism is the adjoint transpose, along `(f')^* ⊣ (f')_*`, of the composite
of the pullback comparison isomorphism with `(g')^*` of the counit of `f^* ⊣ f_*`.  This is the
sense in which the base-change morphism is canonical: it is not a choice of morphism, but the
transpose of a prescribed one. -/
theorem homEquiv_pullbackSquareIso_comp (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M))
        ((Scheme.Modules.pullback g').obj M)
        ((pullbackSquareIso f f' g g' w).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
          (Scheme.Modules.pullback g').map
            ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M := by
  rw [baseChangeNatTrans_app, Adjunction.homEquiv_unit]

/-- The base-change morphism is the *only* morphism with the prescribed adjoint transpose.
Together with `Stacks.Modules.homEquiv_pullbackSquareIso_comp` this pins the base-change
morphism down completely: it is not one isomorphism among many, but the unique morphism
transposing to `(g')^*` of the counit of `f^* ⊣ f_*`. -/
theorem eq_baseChangeNatTrans_app (w : g' ≫ f = f' ≫ g) (M : X.Modules)
    {β : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj M)}
    (h : ((Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _).symm β =
      (pullbackSquareIso f f' g g' w).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)) :
    β = (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _).symm.injective
  rw [h, ← homEquiv_pullbackSquareIso_comp, Equiv.symm_apply_apply]

/-- First triangle identity for the base-change morphism: pulling it back along `f'` and
composing with the counit of `(f')^* ⊣ (f')_*` recovers the pullback comparison isomorphism
followed by `(g')^*` of the counit of `f^* ⊣ f_*`. -/
theorem pullback_map_baseChangeNatTrans_app_comp_counit (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback f').map
          ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app M) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
          ((Scheme.Modules.pullback g').obj M) =
      (pullbackSquareIso f f' g g' w).hom.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  rw [baseChangeNatTrans_eq_mateEquiv]
  exact mateEquiv_counit (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f') (pullbackTwoSquare f f' g g' w) M

/-- Second triangle identity for the base-change morphism: precomposing it with `g^*` of the unit
of `f^* ⊣ f_*` gives the unit of `(f')^* ⊣ (f')_*` followed by `(f')_*` of the pullback
comparison isomorphism. -/
theorem map_unit_comp_baseChangeNatTrans_app (w : g' ≫ f = f' ≫ g) (M : Y.Modules) :
    (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w).app
          ((Scheme.Modules.pullback f).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f').unit.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pushforward f').map
          ((pullbackSquareIso f f' g g' w).hom.app M) := by
  rw [baseChangeNatTrans_eq_mateEquiv]
  exact unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f') (pullbackTwoSquare f f' g g' w) M

end Bridge

/-- The self-base-change morphism of Tag 07TT unfolds to the base-change morphism of the square
of the two projections of `W ×_X W`:  it is a value of
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, not a further construction. -/
theorem selfBaseChange_eq {W : Scheme.{u}} (f : W ⟶ X) (G : W.Modules) :
    selfBaseChange f G =
      (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans (snd_comp_self f)).app G :=
  rfl

end Stacks.Modules

end
