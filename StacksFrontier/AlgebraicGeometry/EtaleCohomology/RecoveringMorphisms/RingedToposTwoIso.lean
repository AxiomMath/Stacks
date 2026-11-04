module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion

/-!
# Faithfulness of the small étale ringed topos, in the 2-category of ringed topoi

Let `X` and `Y` be schemes of a big étale site.  A morphism of schemes `a : X ⟶ Y` induces a
morphism of small étale ringed topoi `(a_small, a_small^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)`,
and Stacks 04LW says that two morphisms of schemes whose induced morphisms of ringed topoi are
2-isomorphic are equal.  Equivalently, a morphism of ringed topoi between the small étale ringed
topoi of `X` and `Y` is 2-isomorphic to `(f_small, f_small^♯)` for at most one `f : X ⟶ Y`.

## Main definitions

* `AlgebraicGeometry.smallEtaleRingedToposHom` — the morphism of small étale ringed *topoi* of a
  morphism of schemes, Stacks 070R part (2) read through
  `AlgebraicGeometry.RingedSite.HomGeneral.toRingedToposHom`.

## Main results

* `AlgebraicGeometry.eq_of_smallEtaleRingedToposHom_twoIso` — Stacks 04LW, with the hypothesis a
  `AlgebraicGeometry.RingedToposHom.TwoIso` rather than its data spelled out.
* `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom` — the uniqueness clause of
  Stacks 04I6, and, since the schemes are arbitrary, also that of Stacks 04I7.

## Implementation notes

`AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom` is stated for arbitrary schemes of the
big étale site and for an arbitrary morphism of ringed topoi between their small étale ringed
topoi. So it is the uniqueness clause of Stacks 04I7 verbatim, and a fortiori that of
Stacks 04I6, which is the case of two affine schemes and of a morphism of *locally* ringed
topoi; no affineness and no local-ringedness hypothesis is used. Both tags are therefore
recorded on it rather than restated, the existence clauses being elsewhere.

## References

* [Stacks Project, Tag 04LW](https://stacks.math.columbia.edu/tag/04LW)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}

/-- The morphism of small étale *ringed topoi* `(a_small, a_small^♯) : (X_étale, 𝒪_X) ⟶
(Y_étale, 𝒪_Y)` of a morphism of schemes `a : X ⟶ Y`. -/
@[stacks 070R "part (2), read in the 2-category of ringed topoi"]
def smallEtaleRingedToposHom (a : X ⟶ Y) :
    RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)) :=
  (smallEtaleRingedSiteHom B a).toRingedToposHom

/-- The direct image of `(a_small, a_small^♯)` is small étale base change. -/
@[simp]
theorem smallEtaleRingedToposHom_pushforward (a : X ⟶ Y) :
    (smallEtaleRingedToposHom B a).toToposHom.pushforward =
      (smallEtaleBaseChange B a).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) :=
  rfl

/-- Forgetting the ring operations of the structure map of `(a_small, a_small^♯)` gives
`AlgebraicGeometry.structureSharp`, pullback of global functions along the base-change
projection. -/
theorem forgetFSharp_smallEtaleRingedToposHom (a : X ⟶ Y) :
    RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B a) =
      (sheafCompose (SmallEtale.topology B Y.obj Y.property) (forget CommRingCat.{u})).map
        (structureSharp B a) :=
  rfl

/-- **Stacks 04LW**, in the 2-category of ringed topoi.  Two morphisms of schemes `a, b : X ⟶ Y`
for which `(a_small, a_small^♯)` and `(b_small, b_small^♯)` are 2-isomorphic are equal. -/
@[stacks 04LW]
theorem eq_of_smallEtaleRingedToposHom_twoIso (a b : X ⟶ Y)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B a)
      (smallEtaleRingedToposHom B b)) :
    a = b := by
  refine eq_of_smallEtale_twoIso_comm B a b t.e ?_
  have h := t.commutes
  rw [forgetFSharp_smallEtaleRingedToposHom, forgetFSharp_smallEtaleRingedToposHom] at h
  exact h

/-- **The uniqueness half of Stacks 04I6.**  A morphism of ringed topoi between the small étale
ringed topoi of two schemes is 2-isomorphic to `(f_small, f_small^♯)` for at most one morphism
of schemes `f : X ⟶ Y`. -/
@[stacks 04LW "the uniqueness clause of 04I6"]
theorem eq_of_twoIso_smallEtaleRingedToposHom
    (g : RingedToposHom
      (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
    (a b : X ⟶ Y)
    (ta : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B a))
    (tb : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B b)) :
    a = b :=
  eq_of_smallEtaleRingedToposHom_twoIso B a b (ta.symm.trans tb)

add_to_stacks 04I6 "the uniqueness clause: for two affine schemes and a morphism of locally
  ringed topoi, which this statement covers since it assumes neither"
  AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom

add_to_stacks 04I7 "the uniqueness clause, i.e. the faithfulness half of the full faithfulness
  asserted by the theorem"
  AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom

end AlgebraicGeometry

end
