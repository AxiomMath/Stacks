module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomLocallyBijective

/-!
# An equivalence over the base survives the morphism-universe lift

Let `p : 𝒜 ⥤ 𝒞` and `r : ℬ ⥤ 𝒞` be categories over `𝒞` and let `K : 𝒜 ⥤ ℬ` be an equivalence over
`𝒞`. Then the morphism-universe lift `K⁺ : ULiftHom 𝒜 ⥤ ULiftHom ℬ` of
`CategoryTheory.Functor.uliftHomMap` is again an equivalence over `𝒞`.

Nothing happens: raising the morphism universe is an equivalence of categories commuting strictly
with the projection to `𝒞`, the fibres of a category and of its lift have the same objects, and the
isomorphisms of a fibre correspond. So the data of
`CategoryTheory.Functor.isEquivalenceOver_of_exists_vertical_iso` — full faithfulness and a
vertical preimage for every object — transports term by term.

This is what the recognition criterion of Stacks 02ZN and 02ZP needs: it consumes its hypotheses at
the morphism universe the explicit stackification works in, which is one above the morphism
universe of the site, so a presentation offered to it has to be compared with the expected one at
the raised universe.

## Main results

* `CategoryTheory.Functor.full_uliftHomDown` and
  `CategoryTheory.Functor.faithful_uliftHomDown`: forgetting the morphism-universe lift is fully
  faithful.
* `CategoryTheory.Functor.isHomLift_uliftHomProj_up`: a morphism lying over `f` still does after
  the lift.
* `CategoryTheory.Functor.hasVerticalPreimages_uliftHomMap`: vertical preimages transport.
* `CategoryTheory.Functor.isEquivalenceOver_uliftHomMap`: the lift of an equivalence over `𝒞` is
  an equivalence over `𝒞`.

## Implementation notes

`CategoryTheory.ULiftHom C` is a type alias for `C` and `CategoryTheory.ULiftHom.objUp` and
`CategoryTheory.ULiftHom.objDown` are the identity, so an object of the lift *is* an object of the
original and the comparison isomorphisms below are the images of the original ones under
`CategoryTheory.ULiftHom.up`, with no transport to insert. Only the morphisms change, and they
change by a `ULift` wrapper that `CategoryTheory.ULiftHom.up` and `CategoryTheory.ULiftHom.down`
add and remove.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 042V](https://stacks.math.columbia.edu/tag/042V)
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory

universe v₁ u₁ v₂ u₂ u₃ v₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  {ℬ : Type u₃} [Category.{v₂} ℬ]

/-! ### Forgetting the morphism-universe lift is fully faithful -/

/-- Forgetting the morphism-universe lift is a full functor: a morphism of the original category is
the image of its own lift. -/
theorem full_uliftHomDown : (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜).Full where
  map_surjective := fun {_ _} f ↦ ⟨⟨f⟩, rfl⟩

/-- Forgetting the morphism-universe lift is a faithful functor. -/
theorem faithful_uliftHomDown : (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜).Faithful where
  map_injective := fun {_ _ _ _} h ↦ ULift.ext _ _ h

/-! ### Lying over a morphism of `𝒞` survives the lift -/

/-- A morphism lying over `f` for `r` has its lift lying over `f` for the lift of `r`: the
projection of the lift sends the lifted morphism to the same morphism of `𝒞`. -/
theorem isHomLift_uliftHomProj_up {r : ℬ ⥤ 𝒞} {R S : 𝒞} {x y : ℬ} (f : R ⟶ S) (φ : x ⟶ y)
    (h : r.IsHomLift f φ) :
    (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞).IsHomLift f
      ((ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ).map φ) := by
  cases h
  exact _root_.CategoryTheory.IsHomLift.map _ ((ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ).map φ)

/-! ### Vertical preimages transport -/

/-- **Vertical preimages transport to the morphism-universe lift.** An object of the lift of `ℬ` is
an object of `ℬ`; its preimage in `𝒜` lies over the same object of `𝒞` after the lift, and the
comparison isomorphism is the image of the original one, which still lies over an identity. -/
theorem hasVerticalPreimages_uliftHomMap {p : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {K : 𝒜 ⥤ ℬ}
    (h : HasVerticalPreimages p r K) :
    HasVerticalPreimages (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞)
      (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞) (uliftHomMap K : ULiftHom.{v₃} 𝒜 ⥤ ULiftHom.{v₃} ℬ) :=
  fun y ↦
    let ⟨o, ho, α, hv⟩ := h (ULiftHom.objDown y)
    ⟨ULiftHom.objUp o, ho,
      (ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ).mapIso α,
      isHomLift_uliftHomProj_up _ _ hv⟩

/-! ### The lift of an equivalence over the base -/

/-- **The morphism-universe lift of an equivalence over `𝒞` is an equivalence over `𝒞`.** The lift
is the composite of forgetting the lift, the equivalence and taking the lift, so it is fully
faithful, and vertical preimages transport. -/
noncomputable def isEquivalenceOver_uliftHomMap {p : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {K : 𝒜 ⥤ ℬ}
    (hK : K ⋙ r = p) (hfull : K.Full) (hfaith : K.Faithful)
    (h : HasVerticalPreimages p r K) :
    IsEquivalenceOver (uliftHomProj p : ULiftHom.{v₃} 𝒜 ⥤ 𝒞)
      (uliftHomProj r : ULiftHom.{v₃} ℬ ⥤ 𝒞)
      (uliftHomMap K : ULiftHom.{v₃} 𝒜 ⥤ ULiftHom.{v₃} ℬ) :=
  haveI := hfull
  haveI := hfaith
  haveI : (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜).Full := full_uliftHomDown
  haveI : (ULiftHom.down : ULiftHom.{v₃} 𝒜 ⥤ 𝒜).Faithful := faithful_uliftHomDown
  haveI : (ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ).Full := full_uliftHomUp
  haveI : (ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ).Faithful := faithful_uliftHomUp
  isEquivalenceOver_of_exists_vertical_iso
    (show (uliftHomMap K : ULiftHom.{v₃} 𝒜 ⥤ ULiftHom.{v₃} ℬ) ⋙ uliftHomProj r =
        uliftHomProj p by
      rw [uliftHomMap, uliftHomProj, uliftHomProj, Functor.assoc, Functor.assoc,
        show (ULiftHom.up : ℬ ⥤ ULiftHom.{v₃} ℬ) ⋙ ULiftHom.down ⋙ r = r from
          (Functor.assoc _ _ _).symm.trans ((Functor.comp_id r).symm ▸ rfl), hK])
    (hasVerticalPreimages_uliftHomMap h)

end CategoryTheory.Functor

end
