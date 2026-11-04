module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The sheaf condition on the site of the charts of the members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X`.
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/FullnessViaSigmaSite.lean` builds the
site of the charts of the members of that family: the category
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite` of pairs of a member and a chart of it,
with the morphisms of the induced charts of `X`, and on it the topology
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTopology` **restricted** from the small étale
topology of `X` along `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor`.

This file reads the sheaf condition on that site.  Its covering sieves are, by definition, the ones
the restriction creates, and nothing about them is stated where the site is built; so a presheaf of
abelian groups on the charts of the members — the shape in which a descent datum for quasi-coherent
modules presents itself, by
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/MemberSiteOfPresheaf.lean` — has no
usable sheaf condition until the covering sieves are read on the small étale site of `X`, where the
étale coverings live.  **That reading is what this file supplies**, for an arbitrary presheaf of
abelian groups on the site, together with the two instantiations that need no further mathematics.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.mem_memberTopology_iff`: **a sieve of the site of
  the charts of the members is covering exactly when its image generates a covering sieve of the
  induced chart of `X`.**  The restricted topology is *a priori* only the coarsest topology
  containing those sieves; it contains no others because `.memberFunctor` is fully faithful and
  cover dense, which makes it a dense subsite.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberTopology_iff`: **the sheaf condition
  for a presheaf of abelian groups on the charts of the members, read on the small étale site of
  `X`.**  This is `CategoryTheory.Presheaf.IsSheaf` with membership in `.memberTopology` replaced
  by the condition on the image sieve.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberTopology_iff_isSheafFor`: the same
  condition on **presieves**, which is the form a covering family is given in — a family of
  morphisms of the site whose image is an étale covering of the induced chart of `X`, together with
  its pullbacks along the morphisms of the site.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheafFor_of_isSheaf_memberTopology`: a sheaf on
  the charts of the members glues over every family of morphisms of the site whose image is an
  étale covering family of the induced chart of `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberFunctor_op_comp`: a sheaf of abelian
  groups on the small étale site of `X` stays a sheaf when read on the charts of the members.  This
  is the one half of the sheaf condition on this site that needs no descent datum: `.memberFunctor`
  is continuous for the restricted topology.

## Implementation notes

**Which Mathlib predicate.**  `CategoryTheory.Presheaf.IsSheaf` is the one, and it is forced from
above: a `CategoryTheory.SheafOfModules` over the structure sheaf read on the charts of the members
asks exactly for `Presheaf.IsSheaf (memberTopology …) M.presheaf` of the underlying presheaf of
abelian groups of its `CategoryTheory.PresheafOfModules`, and
`CategoryTheory.PresheafOfModules.ofPresheaf_presheaf` says that underlying presheaf is the
presheaf of abelian groups one starts from, on the nose.  So the statements below are literally the
obligation of the next step, with no transport in between.

The element-level reformulation `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` is **not**
available here and is not used: it asks for limits of the size of the site in the target category,
and the site of the charts of the members has more objects than `AddCommGrpCat.{u}` has limits.
What replaces it is `CategoryTheory.Presheaf.IsSheaf`'s own definition — the condition on
`P ⋙ coyoneda.obj (op E)` for every abelian group `E` — which is where the statements below leave
it, since that is a condition on `Type`-valued presheaves and every gluing tool applies to it.

**Nothing here is about a descent datum.**  Every statement is for an arbitrary presheaf of abelian
groups on the site, so each one instantiates at the presheaf a descent datum carries without any
further elaboration; none of them inspects a transition, and none of them can, since the covering
sieves of the site do not mention one.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.  In
particular the effectivity clause of Stacks 04W6 is not asserted.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The covering sieves of the site of the charts of the members -/

/-- **A sieve of the site of the charts of the members is covering exactly when its image
generates a covering sieve of the induced chart of `X`.**  One direction is the definition of the
restricted topology; the other holds because `.memberFunctor` is fully faithful — it is an induced
functor — and cover dense, so it exhibits the charts of the members as a *dense subsite* of the
small étale site of `X`, where the restricted topology creates no covering sieve beyond the ones it
is generated by. -/
theorem mem_memberTopology_iff {p : MemberSite B S hS Yi f hf} {T : Sieve p} :
    T ∈ memberTopology B S hS Yi f hf p ↔
      T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
        SmallEtale.topology B S hS X.1 ((memberFunctor B S hS Yi f hf).obj p) :=
  Functor.mem_restrictedTopology_iff

/-! ### The sheaf condition -/

/-- **The sheaf condition for a presheaf of abelian groups on the site of the charts of the
members, read on the small étale site of `X`.**  By `.mem_memberTopology_iff` the covering sieves
of the site are those whose image generates a covering sieve of the induced chart of `X`, so this
is `CategoryTheory.Presheaf.IsSheaf` with its hypothesis stated where the étale coverings live.

The condition on the right is on the `Type`-valued presheaves `P ⋙ coyoneda.obj (op E)`, which is
what `CategoryTheory.Presheaf.IsSheaf` asks of a presheaf with values in an arbitrary category;
the element-level form of it is not available at these universes, see the implementation notes. -/
theorem isSheaf_memberTopology_iff (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P ↔
      ∀ (E : AddCommGrpCat.{u}) (p : MemberSite B S hS Yi f hf) (T : Sieve p),
        T.functorPushforward (memberFunctor B S hS Yi f hf) ∈
            SmallEtale.topology B S hS X.1 ((memberFunctor B S hS Yi f hf).obj p) →
          Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E)) (T : Presieve p) := by
  constructor
  · intro hP E _ T hT
    exact hP E T (mem_memberTopology_iff B S hS Yi f hf |>.2 hT)
  · intro h E p T hT
    exact h E p T (mem_memberTopology_iff B S hS Yi f hf |>.1 hT)

/-- **The sheaf condition for a presheaf of abelian groups on the site of the charts of the
members, indexed by the covering sieves of the small étale site of `X`.**  A covering sieve of a
chart of `X` pulls back to a covering sieve of the charts of the members, and every covering sieve
of the charts of the members is such a pullback — `.memberFunctor` is fully faithful, so pulling
back its own pushforward returns the sieve one started with.  So this is the sheaf condition with
its quantifier moved to where the étale coverings are: one gluing obligation per étale covering
sieve of the induced chart of `X`. -/
theorem isSheaf_memberTopology_iff_functorPullback
    (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P ↔
      ∀ (E : AddCommGrpCat.{u}) (p : MemberSite B S hS Yi f hf)
        (T : Sieve ((memberFunctor B S hS Yi f hf).obj p)),
        T ∈ SmallEtale.topology B S hS X.1 ((memberFunctor B S hS Yi f hf).obj p) →
          Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E))
            (T.functorPullback (memberFunctor B S hS Yi f hf) : Presieve p) := by
  rw [isSheaf_memberTopology_iff]
  constructor
  · intro h E p T hT
    exact h E p _ (Functor.LocallyCoverDense.functorPushforward_functorPullback_mem ⟨T, hT⟩)
  · intro h E p T hT
    have h' := h E p (T.functorPushforward (memberFunctor B S hS Yi f hf)) hT
    rwa [Sieve.functorPullback_functorPushforward_eq] at h'

/-- **The sheaf condition for a presheaf of abelian groups on the site of the charts of the
members, on presieves.**  A covering family of a chart of a member is given as a *family* of
morphisms of the site, not as a sieve, and the topology of the site is generated by such families;
this is the sheaf condition in those terms — unique gluing over the pullback of each family whose
image generates a covering sieve of the induced chart of `X`.

The pullbacks cannot be dropped: the topology is the Grothendieck topology *generated* by those
families, and `CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff` is where the generation is
paid for. -/
theorem isSheaf_memberTopology_iff_isSheafFor
    (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P ↔
      ∀ (E : AddCommGrpCat.{u}) {p q : MemberSite B S hS Yi f hf} {k : q ⟶ p}
        (R : Presieve p),
        Sieve.generate (R.map (memberFunctor B S hS Yi f hf)) ∈
            SmallEtale.topology B S hS X.1 ((memberFunctor B S hS Yi f hf).obj p) →
          Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E))
            ((Sieve.generate R).pullback k).arrows := by
  constructor
  · intro hP E _ _ _ R hR
    exact (Precoverage.isSheaf_toGrothendieck_iff _).1 (hP E) R
      ((GrothendieckTopology.mem_toPrecoverage_iff _ _).2 hR)
  · intro h E
    refine (Precoverage.isSheaf_toGrothendieck_iff _).2 ?_
    intro _ _ k R hR
    exact h E (k := k) R ((GrothendieckTopology.mem_toPrecoverage_iff _ _).1 hR)

/-- **A sheaf of abelian groups on the site of the charts of the members glues over every family
of morphisms of the site whose image is an étale covering family of the induced chart of `X`.**
This is the direction of the sheaf condition a consumer uses: the hypothesis is a covering family
in the sense of `AlgebraicGeometry.Space.SmallEtale.IsCovering`, which is how an étale covering of
a chart of `X` is produced. -/
theorem isSheafFor_of_isSheaf_memberTopology
    {P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hP : Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P) (E : AddCommGrpCat.{u})
    {p : MemberSite B S hS Yi f hf} (R : Presieve p)
    (hR : R.map (memberFunctor B S hS Yi f hf) ∈
      SmallEtale.precoverage B S hS X.1 ((memberFunctor B S hS Yi f hf).obj p)) :
    Presieve.IsSheafFor (P ⋙ coyoneda.obj (Opposite.op E)) R :=
  (hP E).isSheafFor R (mem_memberTopology_iff B S hS Yi f hf |>.2 (by
    rw [← Sieve.generate_map_eq_functorPushforward]
    exact Precoverage.generate_mem_toGrothendieck hR))

/-- **A sheaf of abelian groups on the small étale site of `X` stays a sheaf when read on the
charts of the members.**  The topology of the charts of the members is restricted along
`.memberFunctor`, which is fully faithful and cover dense, hence a dense subsite and in particular
continuous; and a continuous functor pulls sheaves back to sheaves.

This is the half of the sheaf condition on this site that holds for no reason to do with a descent
datum, and it is what makes the restriction of an `𝒪_X`-module to the charts of the members a sheaf
of modules there. -/
theorem isSheaf_memberFunctor_op_comp (Q : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hQ : Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) Q) :
    Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
      ((memberFunctor B S hS Yi f hf).op ⋙ Q) :=
  (memberFunctor B S hS Yi f hf).op_comp_isSheaf_of_isSheaf
    (memberTopology B S hS Yi f hf) (SmallEtale.topology B S hS X.1) Q hQ

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
