module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitSheafAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Stacks 0EYN, second half, on Mathlib's small étale site of the limit

`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToSmallEtale` proves the
colimit half of [Stacks, Tag 0EYN] for abelian sheaves on the *size-bounded* small étale site
`AlgebraicGeometry.SmallEtale.topology B X hX` of the limit `X = lim X_i`. The statements that
consume it — the hypothesis `h0EYN` of [Stacks, Tag 0DV2] in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LimitHigherDirectImageColimit.lean`, and
the presentation predicate of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitPresentation.lean` — are
about sheaves on *Mathlib's* small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology X`,
whose site is `AlgebraicGeometry.Scheme.Etale X` and not the bounded category of
[Stacks, Tag 021B].

This file carries the descent across that crossing, at the limit: it restates
`restrictionIsColimitAb_limitToSmallEtale` for a sheaf on Mathlib's site, restriction being taken
along the composite of the two bounded-site crossings with
`AlgebraicGeometry.SmallEtale.toEtaleSite`.

## Main results

* `AlgebraicGeometry.SmallEtale.full_etaleSiteRestriction`,
  `AlgebraicGeometry.SmallEtale.faithful_etaleSiteRestriction` — restriction of sheaves along the
  embedding of the size-bounded small étale site into Mathlib's is fully faithful, at an arbitrary
  coefficient category with limits of the size of the schemes. It is the inverse of
  `AlgebraicGeometry.SmallEtale.sheafEquiv`.
* `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToEtaleSite` —
  **[Stacks, Tag 0EYN], second half, for abelian sheaves on Mathlib's small étale site of the
  limit.**

## Implementation notes

**Nothing is weakened and nothing is assumed.** The crossing is an equivalence of sheaf
categories, `AlgebraicGeometry.SmallEtale.sheafEquiv`, whose inverse is exactly restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite`; a universal property stated for a sheaf transports
along it in both directions. Concretely: the family of maps on the levels is literally the same
data on both sides, the three functors it is a restriction along composing associatively, so only
two things are done. The reindexing isomorphisms of the compatibility hypothesis are matched by
`InverseSystemOfFiniteSites.map_eqToHom_sheafPushforwardContinuous` (in the namespace
`CategoryTheory.Sites.InverseSystem`), which says that reindexing a restricted sheaf is reindexing
along the image identification. And the morphism `h` is produced from the one the bounded statement
gives by fullness of restriction and shown unique by its faithfulness.

**What this does *not* do.** It crosses from the bounded site to Mathlib's at the LIMIT only. The
levels of `Stacks.EtaleCohomology.AffineLimitCohomology.sys` are still categories of chosen
pullback models, and nothing *here* identifies
`Stacks.EtaleCohomology.AffineLimitCohomology.toLimitSmall i` composed with the crossing with base
change along `c.π.app i` on Mathlib's small étale sites. That identification is proved
elsewhere, as
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitLevelCrossing.lean`, with
its reading on sheaves `…levelRestrictionIso`; it is proved from the fibre-product square
`Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimit_isPullback` that [Stacks, Tag 0EYL]
supplies as data, so it assumes nothing; and the statement below read through it is
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange`. What still
separates this from
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent` is therefore only the
coherence of `Stacks.EtaleCohomology.coneDirectImageCompAb` with the reindexings of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'`. The
transition datum is no longer part of the gap: the identity `D.u a ⋙ u i = u j` holds on the nose
for the system's own functors and only up to the base-change comparison once the levels are read
through `levelCrossingIso`, but the predicate asks for an *isomorphism* and so accepts both.

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe vA uA v₁ u₁ v₂ u₂ v u

namespace CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

/-- **Reindexing a restricted sheaf along an identification of objects is reindexing along the
image identification.** This is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.map_eqToHom_sheafPushforward'` with
the source topology taken as a Grothendieck topology outright rather than as the topology
generated by a precoverage, which is the shape the bounded small étale site comes in. -/
theorem map_eqToHom_sheafPushforwardContinuous {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] (T : C₁ ⥤ C₂) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂) [T.IsContinuous J₁ J₂] (A : Type uA) [Category.{vA} A]
    (F : Sheaf J₂ A) {Z Z' : C₁} (e : Z = Z') :
    ((T.sheafPushforwardContinuous A J₁ J₂).obj F).obj.map (eqToHom (congrArg op e)) =
      F.obj.map (eqToHom (congrArg op (congrArg T.obj e))) := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, Functor.map_id, Functor.map_id]
  rfl

end CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

/-! ### Restriction along the embedding of the size-bounded small étale site -/

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (A : Type uA) [Category.{vA} A] [HasLimitsOfSize.{u, u} A]

/-- **Restriction of sheaves along the embedding of the size-bounded small étale site of
[Stacks, Tag 021B] into Mathlib's.** It is the inverse of
`AlgebraicGeometry.SmallEtale.sheafEquiv`, spelled as a restriction functor. -/
abbrev etaleSiteRestriction :
    Sheaf S.smallEtaleTopology A ⥤ Sheaf (topology B S hS) A :=
  (toEtaleSite B S hS).sheafPushforwardContinuous A (topology B S hS) S.smallEtaleTopology

/-- Restriction along the embedding of the bounded small étale site is full: it is the inverse of
the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
instance full_etaleSiteRestriction : (etaleSiteRestriction B S hS A).Full := by
  have h : etaleSiteRestriction B S hS A = (sheafEquiv B S hS A).inverse := rfl
  rw [h]
  infer_instance

/-- Restriction along the embedding of the bounded small étale site is faithful, for the same
reason as `AlgebraicGeometry.SmallEtale.full_etaleSiteRestriction`. -/
instance faithful_etaleSiteRestriction : (etaleSiteRestriction B S hS A).Faithful := by
  have h : etaleSiteRestriction B S hS A = (sheafEquiv B S hS A).inverse := rfl
  rw [h]
  infer_instance

end AlgebraicGeometry.SmallEtale

/-! ### The colimit half of Stacks 0EYN on Mathlib's small étale site of the limit -/

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **[Stacks, Tag 0EYN], second half, on Mathlib's small étale site of a limit of schemes, for
sheaves of ABELIAN GROUPS.** Let `(X_i)` be an inverse system of schemes with affine transition
morphisms over a nonempty directed index, all of them objects of a big étale site `B`, let
`X = lim X_i`, and let `F` be an abelian sheaf on *Mathlib's* small étale site of `X`. Then

`F = colim_i p_i^{-1} p_{i, *} F`,

in the form the inverse-system machinery proves it: every family of maps out of the restrictions
of `F` to the levels of the system of sites of [Stacks, Tag 0EYL], compatible with the canonical
reindexings, is the restriction of a **unique** map of sheaves out of `F`.

This is `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToSmallEtale`
with the size-bounded small étale site of [Stacks, Tag 021B] replaced by Mathlib's, the two being
carried by the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` whose inverse is restriction
along `AlgebraicGeometry.SmallEtale.toEtaleSite`. Restriction along that embedding is fully
faithful (`AlgebraicGeometry.SmallEtale.full_etaleSiteRestriction`,
`faithful_etaleSiteRestriction`), which is what produces the morphism and its uniqueness; the
family of maps on the levels is the same data on both sides. -/
theorem restrictionIsColimitAb_limitToEtaleSite
    (F : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1}) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (c.pt).smallEtaleTopology
      AddCommGrpCat.{max u v + 1} (sys D c B hD hX hc)
      (fun i => toLimitSmall D c B hD hX hc i ⋙
        (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX))
      (InverseSystemOfFiniteSites.compTransitionIso
        (limitToSmallEtale D c B hX ⋙ AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
        (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)) F := by
  intro H g hg
  obtain ⟨h₀, hh₀, hu₀⟩ :=
    restrictionIsColimitAb_limitToSmallEtale D c B hD hX hc
      ((AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
        AddCommGrpCat.{max u v + 1}).obj F)
      ((AlgebraicGeometry.SmallEtale.etaleSiteRestriction B c.pt hX
        AddCommGrpCat.{max u v + 1}).obj H) g
      (by
        intro i j a V
        refine Eq.trans (hg a V) ?_
        simp only [InverseSystemOfFiniteSites.map_op_compTransitionIso_hom_app,
          InverseSystemOfFiniteSites.map_op_compTransitionIso_inv_app]
        have key (G : Sheaf (c.pt).smallEtaleTopology AddCommGrpCat.{max u v + 1})
            {Z Z'} (e : Z = Z') :=
          InverseSystemOfFiniteSites.map_eqToHom_sheafPushforwardContinuous
            (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX)
            (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (c.pt).smallEtaleTopology
            AddCommGrpCat.{max u v + 1} G e
        have e := congrArg (limitToSmallEtale D c B hX).obj
          (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) V)
        rw [key F e.symm, key H e]
        rfl)
  obtain ⟨h, rfl⟩ := Functor.map_surjective _ h₀
  exact ⟨h, fun i V => hh₀ i V, fun y hy => Functor.map_injective _ (hu₀ _ fun i V => hy i V)⟩

end Stacks.EtaleCohomology.AffineLimitCohomology

end
