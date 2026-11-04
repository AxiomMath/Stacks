module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleAffineSheafEquiv

/-!
# Stacks 0EYN, second half: a sheaf on the limit is the colimit of the pullbacks of its
direct images

Let `I` be a nonempty directed preorder, let `(X_i)` be an inverse system of schemes over `I` whose
transition morphisms are affine, let `X = lim X_i` and write `p_i : X ⟶ X_i` for the projections.
Stacks 0EYN asserts two things about a sheaf of sets `𝓕` on the small étale site of `X`: that the
direct images `p_{i,*}𝓕` form a system of sheaves, and that

`𝓕 = colim_i p_i^{-1} p_{i,*}𝓕`

with the counits as structure maps. The first half is
`Stacks.EtaleCohomology.directImageSystem`; this file proves the second, on the size-bounded small
étale site of Stacks 021B, for sheaves of sets in `Type (max u v + 1)`.

## Main results

* `CategoryTheory.AsSmall.isContinuous_down`, `CategoryTheory.AsSmall.isContinuous_up` — the
  universe-raising functors of `CategoryTheory.AsSmall` are continuous between a precoverage and
  its comap, in both directions.
* `CategoryTheory.AsSmall.sheafRaise` — the resulting transport of sheaves onto the raised site,
  which is restriction along `AsSmall.down` on the nose, together with the `Full` and `Faithful`
  instances that make it a bijection on morphisms.
* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction` —
  **Stacks 0EYN, second half**, in transported form: for a continuous `Λ : C ⥤ E` along which
  restriction of sheaves of sets is fully faithful, a compatible family of maps on the levels of
  the system, read through `u i ⋙ Λ`, is the restriction of a unique map of sheaves on `(E, J)`.
  `CategoryTheory.Functor.existsUnique_of_fullyFaithful` is the transfer it runs on.
* `Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale`,
  `levelFunctor`, `levelFunctor_transition`, `isContinuous_limitToSmallEtale`,
  `full_limitRestriction`, `faithful_limitRestriction`, `raiseFunctor`, `raisedSheaf`,
  `levelRestrict` — the two crossings carried out for the system of sites of Stacks 0EYL, so that
  `descent_along_restriction` applies with `Λ = limitToSmallEtale` and `E` the small étale site of
  the limit. `levelRestrict_eq_raised` and `levelRestrict_obj` record that the identifications are
  definitional.
* `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimit_limitToSmallEtale` —
  **Stacks 0EYN, second half, at the geometry**: the instantiation of `descent_along_restriction`
  for the system of sites of Stacks 0EYL, so that `𝓕 = colim_i p_i^{-1}p_{i,*}𝓕` holds for every
  sheaf of sets on the small étale site of the limit, with no hypothesis beyond the limit cone
  and the affineness of the transition morphisms. The restrictions it speaks of are the
  `p_{i,*}𝓕` read on the levels, which is `levelRestrict`. Its four site inputs are bundled as
  `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.ColimitSiteInputs` and supplied
  by `Stacks.EtaleCohomology.AffineLimitCohomology.colimitSiteInputs_toLimitSmall`.

## Implementation notes

**The instantiation is split in two, and that is what makes it fit the budget.** Feeding the site
inputs of the machinery at the concrete system of Stacks 0EYL does not fit the elaborator's
200000 heartbeats in one declaration: writing the conclusion out exhausts
the budget in the *signature* (a `(deterministic) timeout at isDefEq` inside the compatibility
hypothesis of the family `g`, before any proof runs), and naming the conclusion moves the same
failure into the proof, as a `whnf` timeout over the whole telescope. The cost is cumulative over
the arguments, every one of which is cheap on its own; raising an option is not available. Two
packagings cure it, and both are instances of a rule this development has now needed five times —
state it about variables, and pay for a concrete instance in a declaration of its own:

* `RestrictionIsColimit` names the conclusion, so the signature mentions the system twice instead
  of thirty times. Its legs are an arbitrary family of functors from the levels to the ambient
  site and its transition datum is an **isomorphism** rather than the equality of
  [Stacks, Tag 0A34];
  `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.compTransitionIso` supplies the
  equality case, so this is a generalisation and not a weakening, and what it buys is that the
  predicate can be read where the two readings of a level agree only up to a canonical
  isomorphism — as they do once the levels are read as base changes;
* `ColimitSiteInputs` bundles the four site inputs, so the matching of each against its geometric
  counterpart is paid in `colimitSiteInputs_toLimitSmall` rather than together with everything
  else.

The machinery of Stacks 09YN
(`Sites.InverseSystem.InverseSystemOfFiniteSites.isColimit_pullback_pushforward_of_colimit`) lives
on `AsSmall (SmallAffineEtale B X hX)`, because a colimit of sites must be a *small* category
while the small affine étale site is only locally small. The statements here live on
`SmallEtale B X hX`. Two crossings are therefore needed, and both are cheap precisely because the
machinery is phrased through restriction along the functors `u i` only -- no inverse-image functor
and no sheafification appear in it:

* `AsSmall`: the first section of this file. The tree did not have this; every existing consumer of
  the Stacks 09YP/09YN machinery on the raised site, such as
  `Stacks.EtaleCohomology.QcqsLimitCohomology.globalSections_colimit_of_qcqs_level`, takes the
  sheaf on the raised site as a hypothesis and so never had to build one.
* Stacks 04HR: `AlgebraicGeometry.SmallAffineEtale.sheafEquiv`.

Both crossings are restrictions along functors, so the composite is restriction along the single
functor `levelFunctor`, and the identification of the machinery's `(u i).op ⋙ F.obj` with
`(levelFunctor i).op ⋙ F.obj` holds definitionally.

## References

* [Stacks 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 04HR](https://stacks.math.columbia.edu/tag/04HR)

Tags covered: 0EYN part (2) (`𝓕 = colim_i p_i^{-1}p_{i,*}𝓕`); part (1) is
`Stacks.EtaleCohomology.directImageSystem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂ vA uA v u

namespace CategoryTheory.AsSmall

/-! ### Sheaves on a universe-raised site

`CategoryTheory.AsSmall.{w} C` raises the morphism universe of `C` so that it becomes a small
category; `AsSmall.up` and `AsSmall.down` are mutually inverse *on the nose*. Transporting a site
structure along them is therefore bookkeeping, and this section carries it out at the level of
sheaves: a precoverage `K` on `C` is carried to `K.comap AsSmall.down`, which is how
`Stacks.EtaleCohomology.AffineLimitCohomology.limitSitePrecoverage` is defined. -/

section

variable {C : Type u₁} [Category.{v₁} C]

/-- Pushing a sieve of the raised category down along `AsSmall.down` is the same as pulling it
back along `AsSmall.up`. The point is that `AsSmall.up` is full and surjective on objects, so the
image family is already downward closed. -/
theorem functorPushforward_down (Z : AsSmall.{w} C) (S : Sieve Z) :
    Sieve.functorPushforward (AsSmall.down : AsSmall.{w} C ⥤ C) S =
      Sieve.functorPullback (AsSmall.up : C ⥤ AsSmall.{w} C) S := by
  ext Y f
  refine ⟨?_, fun hf => ⟨AsSmall.up.obj Y, AsSmall.up.map f, 𝟙 _, hf, (Category.id_comp f).symm⟩⟩
  rintro ⟨Z', g, h, hg, rfl⟩
  exact S.downward_closed hg (AsSmall.up.map h)

/-- The companion of `functorPushforward_down` for `AsSmall.up`. -/
theorem functorPushforward_up (X : C) (S : Sieve X) :
    Sieve.functorPushforward (AsSmall.up : C ⥤ AsSmall.{w} C) S =
      Sieve.functorPullback (AsSmall.down : AsSmall.{w} C ⥤ C) S := by
  ext Y f
  refine ⟨?_, fun hf => ⟨AsSmall.down.obj Y, AsSmall.down.map f, 𝟙 _, hf,
    (Category.id_comp f).symm⟩⟩
  rintro ⟨Z', g, h, hg, rfl⟩
  exact S.downward_closed hg (AsSmall.down.map h)

/-- Pushing a presieve up to the raised category and back down returns it. -/
theorem presieve_map_up_down {X : C} (R : Presieve X) :
    (R.map (AsSmall.up : C ⥤ AsSmall.{w} C)).map AsSmall.down = R := by
  refine le_antisymm ?_ fun W f hf => Presieve.map_map (Presieve.map_map hf)
  rintro W f ⟨⟨h⟩⟩
  exact h

/-- `AsSmall.down` carries the coverings of the comap precoverage to coverings. -/
theorem coverPreserving_down (K : Precoverage C) :
    CoverPreserving (K.comap (AsSmall.down : AsSmall.{w} C ⥤ C)).toGrothendieck
      K.toGrothendieck AsSmall.down := by
  refine ⟨fun hS => ?_⟩
  induction hS with
  | of X R hR =>
      rw [← Sieve.generate_map_eq_functorPushforward]
      exact Precoverage.generate_mem_toGrothendieck hR
  | top X =>
      rw [functorPushforward_down]
      exact K.toGrothendieck.top_mem _
  | pullback X R hR Y f ih =>
      rw [functorPushforward_down] at ih ⊢
      exact K.toGrothendieck.pullback_stable (AsSmall.down.map f) ih
  | transitive X R Q hR hQ ihR ihQ =>
      refine K.toGrothendieck.transitive ihR _ fun Y' g hg => ?_
      rw [functorPushforward_down] at hg
      have h₂ := ihQ hg
      rwa [functorPushforward_down] at h₂ ⊢

/-- `AsSmall.up` carries coverings to coverings of the comap precoverage. -/
theorem coverPreserving_up (K : Precoverage C) :
    CoverPreserving K.toGrothendieck
      (K.comap (AsSmall.down : AsSmall.{w} C ⥤ C)).toGrothendieck AsSmall.up := by
  refine ⟨fun hS => ?_⟩
  induction hS with
  | of X R hR =>
      rw [← Sieve.generate_map_eq_functorPushforward]
      refine Precoverage.generate_mem_toGrothendieck (R := R.map AsSmall.up) ?_
      rwa [Precoverage.mem_comap_iff, presieve_map_up_down]
  | top X =>
      rw [functorPushforward_up]
      exact (K.comap (AsSmall.down : AsSmall.{w} C ⥤ C)).toGrothendieck.top_mem _
  | pullback X R hR Y f ih =>
      rw [functorPushforward_up] at ih ⊢
      exact (K.comap AsSmall.down).toGrothendieck.pullback_stable (AsSmall.up.map f) ih
  | transitive X R Q hR hQ ihR ihQ =>
      refine (K.comap AsSmall.down).toGrothendieck.transitive ihR _ fun Y' g hg => ?_
      rw [functorPushforward_up] at hg
      have h₂ := ihQ hg
      rwa [functorPushforward_up] at h₂ ⊢

/-- `AsSmall.down` is a right adjoint, being half of the equivalence `AsSmall.equiv`. -/
public noncomputable instance isRightAdjoint_down :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsRightAdjoint :=
  (AsSmall.equiv (C := C)).toAdjunction.isRightAdjoint

/-- `AsSmall.up` is a right adjoint, being half of the equivalence `AsSmall.equiv.symm`. -/
public noncomputable instance isRightAdjoint_up :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsRightAdjoint :=
  (AsSmall.equiv (C := C)).symm.toAdjunction.isRightAdjoint

/-- Being an equivalence, `AsSmall.down` is representably flat; this is what makes it
compatible-preserving, the second half of continuity. -/
public noncomputable instance representablyFlat_down :
    RepresentablyFlat (AsSmall.down : AsSmall.{w} C ⥤ C) :=
  RepresentablyFlat.of_isRightAdjoint _

/-- Being an equivalence, `AsSmall.up` is representably flat. -/
public noncomputable instance representablyFlat_up :
    RepresentablyFlat (AsSmall.up : C ⥤ AsSmall.{w} C) :=
  RepresentablyFlat.of_isRightAdjoint _

/-- **`AsSmall.down` is a morphism of sites** from the comap precoverage of `K` to `K`. -/
public instance isContinuous_down (K : Precoverage C) :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsContinuous
      (K.comap AsSmall.down).toGrothendieck K.toGrothendieck :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (coverPreserving_down K)

/-- **`AsSmall.up` is a morphism of sites** from `K` to the comap precoverage of `K`. -/
public instance isContinuous_up (K : Precoverage C) :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsContinuous
      K.toGrothendieck (K.comap AsSmall.down).toGrothendieck :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (coverPreserving_up K)

variable (K : Precoverage C) (A : Type u₂) [Category.{v₂} A]

/-- **A sheaf on a site, read on its universe-raised copy**: restriction along `AsSmall.down`. -/
public noncomputable abbrev sheafRaise :
    Sheaf K.toGrothendieck A ⥤
      Sheaf (K.comap (AsSmall.down : AsSmall.{w} C ⥤ C)).toGrothendieck A :=
  AsSmall.down.sheafPushforwardContinuous A
    (K.comap AsSmall.down).toGrothendieck K.toGrothendieck

/-- Raising a sheaf does not change its sections: the underlying presheaf of `sheafRaise.obj F` is
`AsSmall.down.op ⋙ F.obj`, by definition. -/
theorem sheafRaise_obj_obj (F : Sheaf K.toGrothendieck A) :
    ((sheafRaise.{w} K A).obj F).obj = AsSmall.down.op ⋙ F.obj :=
  rfl

/-- Raising a morphism of sheaves acts on components by reindexing along `AsSmall.down`. -/
theorem sheafRaise_map_hom_app {F H : Sheaf K.toGrothendieck A} (h : F ⟶ H)
    (Z : AsSmall.{w} C) :
    ((sheafRaise.{w} K A).map h).hom.app (op Z) = h.hom.app (op (AsSmall.down.obj Z)) :=
  rfl

/-- Raising is faithful: `AsSmall.down` is surjective on objects, so a morphism of sheaves is
determined by the components of its raising. -/
public instance faithful_sheafRaise : (sheafRaise.{w} K A).Faithful where
  map_injective h :=
    Sheaf.hom_ext <| NatTrans.ext <| funext fun W =>
      congrArg (fun t => t.hom.app (op (AsSmall.up.obj W.unop))) h

/-- Raising is full: a morphism between raised sheaves is the raising of its restriction along
`AsSmall.up`, since `AsSmall.up ⋙ AsSmall.down` is the identity. -/
public instance full_sheafRaise : (sheafRaise.{w} K A).Full where
  map_surjective {_F _H} γ :=
    ⟨⟨{ app := fun W => γ.hom.app (op (AsSmall.up.obj W.unop))
        naturality := fun _ _ g => γ.hom.naturality (AsSmall.up.op.map g) }⟩, rfl⟩

end

end CategoryTheory.AsSmall

/-! ### Transporting the descent statement of Stacks 09YN across a restriction functor

The machinery of Stacks 09YN concludes about sheaves on the colimit site itself. What a geometric
consumer has is a sheaf on a *different*, equivalent site -- here the small étale site of the
limit, reached from the raised small affine étale site by the two crossings above. The theorem
below carries the conclusion over, once and for all, for any continuous `Λ` along which
restriction of sheaves is fully faithful. -/

namespace CategoryTheory.Functor

/-- **Transfer of a unique-factorisation statement along a fully faithful functor.** If `Φ` is
full and faithful and the predicates `P` on `F ⟶ H` and `Q` on `Φ F ⟶ Φ H` correspond under `Φ`,
then a unique solution of `Q` gives a unique solution of `P`. -/
theorem existsUnique_of_fullyFaithful
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    (Φ : X ⥤ Y) [Φ.Full] [Φ.Faithful] {F H : X}
    (P : (F ⟶ H) → Prop) (Q : (Φ.obj F ⟶ Φ.obj H) → Prop)
    (hPQ : ∀ h : F ⟶ H, P h ↔ Q (Φ.map h)) (hQ : ∃! k, Q k) :
    ∃! h, P h := by
  obtain ⟨k, hk, hku⟩ := hQ
  exact ⟨Φ.preimage k, (hPQ _).2 (by rwa [Φ.map_preimage]),
    fun y hy => Φ.map_injective ((hku _ ((hPQ y).1 hy)).trans (Φ.map_preimage k).symm)⟩

end CategoryTheory.Functor

namespace CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

open CategoryTheory.Sites.InverseSystem

variable {C : Type w} [SmallCategory C] {E : Type u₂} [Category.{v₂} E]
  (K : Precoverage C) (J : GrothendieckTopology E) (Λ : C ⥤ E)
  [Λ.IsContinuous K.toGrothendieck J]

/-- **The cocone identity of [Stacks, Tag 0A34], composed with the crossing `Λ`.** The functors
`u i ⋙ Λ` from the levels to the ambient site inherit, on the nose, the strict cocone identity
the functors `u i` into the small site `C` satisfy.

It is a declaration of its own because the only use a consumer has for it is to form
`CategoryTheory.eqToIso` of it, and an inlined `eqToIso` of the composite `congrArg`
exhausts the heartbeat budget at `isDefEq` when `D` is a concrete system, while
the same equality split off as a theorem of its own costs under a second. -/
theorem comp_transition_eq (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) {i j : D.I} (a : i ⟶ j) :
    D.u a ⋙ (u i ⋙ Λ) = u j ⋙ Λ := by
  rw [← Functor.assoc, hu a]

/-- **The strict cocone identity of [Stacks, Tag 0A34] on the legs `u i ⋙ Λ`, as an
isomorphism.** This is `CategoryTheory.eqToIso` of `comp_transition_eq`, and it is the transition
datum with which `RestrictionIsColimit` and
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'` hold for a
strict cocone. Those predicates ask only for an isomorphism, which is what lets them be
transported into a vocabulary where no equality is available. -/
def compTransitionIso (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) {i j : D.I} (a : i ⟶ j) :
    D.u a ⋙ (u i ⋙ Λ) ≅ u j ⋙ Λ :=
  eqToIso (comp_transition_eq Λ D u hu a)

/-- **Reindexing along the transition isomorphism of a strict cocone is reindexing along the
equality.** With `map_op_compTransitionIso_inv_app`, the bridge between the compatibility
hypotheses of `RestrictionIsColimit` and
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'` and the
`eqToHom` ones that `descent_along_restriction` and `descent_along_restriction'` are stated
with. -/
theorem map_op_compTransitionIso_hom_app {A : Type uA} [Category.{vA} A]
    (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (G : Eᵒᵖ ⥤ A) {i j : D.I} (a : i ⟶ j) (V : D.C j) :
    G.map ((compTransitionIso Λ D u hu a).hom.app V).op =
      G.map (eqToHom (congrArg op (congrArg Λ.obj (Functor.congr_obj (hu a) V).symm))) := by
  simp only [compTransitionIso, eqToIso.hom, eqToHom_app, eqToHom_op]

/-- `map_op_compTransitionIso_hom_app` for the inverse of the identification. -/
theorem map_op_compTransitionIso_inv_app {A : Type uA} [Category.{vA} A]
    (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (G : Eᵒᵖ ⥤ A) {i j : D.I} (a : i ⟶ j) (V : D.C j) :
    G.map ((compTransitionIso Λ D u hu a).inv.app V).op =
      G.map (eqToHom (congrArg op (congrArg Λ.obj (Functor.congr_obj (hu a) V)))) := by
  simp only [compTransitionIso, eqToIso.inv, eqToHom_app, eqToHom_op]

/-- Reindexing a section of a restricted sheaf along an identification of objects of `C` is
reindexing along the image identification in `E`. -/
theorem map_eqToHom_sheafPushforward (F : Sheaf J (Type w)) {Z Z' : C} (e : Z = Z')
    (x : F.obj.obj (op (Λ.obj Z))) :
    ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F).obj.map
        (eqToHom (congrArg op e)) x =
      F.obj.map (eqToHom (congrArg op (congrArg Λ.obj e))) x := by
  subst e
  simp only [eqToHom_refl, Functor.sheafPushforwardContinuous_obj_obj_map, unop_id,
    Functor.map_id, op_id, id_apply]
  rfl

/-- **Stacks 09YN's descent statement, transported along a restriction functor.** In the situation
of Stacks 0A34 let the functors `u i : D.C i ⥤ C` exhibit the small category `C` as the colimit of
the `D.C i` (`hu`, `hobj`, `hhom`, `hhom_inj`) with `K` the coverings of Stacks 09YL (`hK`), and
let `Λ : C ⥤ E` be a continuous functor along which restriction of sheaves of sets is full and
faithful -- the case of interest being the inclusion of a dense subsite composed with a universe
raising.

Let `F` and `H` be sheaves of sets on `(E, J)`, let `ψ` be the transition maps of `F` read on the
levels through `u i ⋙ Λ`, pinned to the canonical identification by `hψ`, and let `g i` be a
family of maps on those restrictions compatible with the `ψ` (`hg`). Then the `g i` are the
restrictions of a **unique** map of sheaves `F ⟶ H`.

This is the half of Stacks 0EYN that says `𝓕 = colim_i f_i^{-1}f_{i,*}𝓕`, in the elementwise form
the machinery proves it: the structure maps are the counits, and the content is that a compatible
family on the levels descends uniquely.

Everything is phrased through restriction along `u i ⋙ Λ`, with no inverse-image functor and no
sheafification, which is what makes the transport free: `Λ` enters only through the restriction
functor, whose action on objects and on morphisms is a composite of functors and therefore
definitional. -/
theorem descent_along_restriction (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
    (hhom :
      ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
        ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
          (u j).map g =
            eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
    (hhom_inj :
      ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
        (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
    (hK :
      ∀ (X : C) (R : Presieve X),
        R ∈ K X ↔
          ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
            S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i))
    [(Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).Full]
    [(Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).Faithful]
    (F H : Sheaf J (Type w))
    (ψ : ∀ {i j : D.I} (a : j ⟶ i),
      (u i ⋙ Λ).op ⋙ F.obj ⟶ (D.u a).op ⋙ ((u j ⋙ Λ).op ⋙ F.obj))
    (hψ : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : F.obj.obj (op ((u i ⋙ Λ).obj V))),
      (ψ a).app (op V) x =
        F.obj.map (eqToHom (congrArg op
          (congrArg Λ.obj (Functor.congr_obj (hu a) V).symm))) x)
    (g : ∀ i, (u i ⋙ Λ).op ⋙ F.obj ⟶ (u i ⋙ Λ).op ⋙ H.obj)
    (hg : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : F.obj.obj (op ((u i ⋙ Λ).obj V))),
      (g i).app (op V) x =
        H.obj.map (eqToHom (congrArg op
          (congrArg Λ.obj (Functor.congr_obj (hu a) V))))
          ((g j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x))) :
    ∃! h : F ⟶ H, ∀ (i : D.I) (V : D.C i) (x : F.obj.obj (op ((u i ⋙ Λ).obj V))),
      (g i).app (op V) x = h.hom.app (op ((u i ⋙ Λ).obj V)) x := by
  have hψ' : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i)
      (x : ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F).obj.obj
        (op ((u i).obj V))),
      (ψ a).app (op V) x =
        ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F).obj.map
          (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) x :=
    fun a V x => (hψ a V x).trans
      (map_eqToHom_sheafPushforward K J Λ F (Functor.congr_obj (hu a) V).symm x).symm
  have hg' : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i)
      (x : ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F).obj.obj
        (op ((u i).obj V))),
      (g i).app (op V) x =
        ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj H).obj.map
          (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
          ((g j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x)) :=
    fun a V x => (hg a V x).trans
      (map_eqToHom_sheafPushforward K J Λ H (Functor.congr_obj (hu a) V) _).symm
  exact (Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).existsUnique_of_fullyFaithful
    _ (fun k => ∀ (i : D.I) (V : D.C i)
      (x : ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F).obj.obj
        (op ((u i).obj V))),
      (g i).app (op V) x = k.hom.app (op ((u i).obj V)) x) (fun _ => Iff.rfl)
    ((isColimit_pullback_pushforward_of_colimit D u hu hobj hhom hhom_inj K hK
      ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj F) ψ hψ').2
      ((Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).obj H) g hg')

/-- **`F = colim_i f_i^{-1}f_{i,*}F` read through a family of functors from the levels to the
ambient site, as a predicate.** The conclusion of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction`
with the two sheaves and the two families universally quantified: every family of maps out of the
restrictions of `F` to the levels along the `v i`, compatible with the transition maps, is the
restriction of a unique map of sheaves out of `F`.

**The transition datum `hv` is an isomorphism, not an equality, and that is a generalisation.**
`descent_along_restriction` proves the statement where the legs `v i` are `u i ⋙ Λ` for a
*strict* cocone `u` of functors into the small site `C`, and there the identification of the two
readings of a level is the equality `D.u a ⋙ u i = u j` of [Stacks, Tag 0A34] composed with `Λ`.
That case is `restrictionIsColimit_of_inputs`, which supplies `compTransitionIso`, i.e.
`CategoryTheory.eqToIso` of it; so asking only for an isomorphism adds no hypothesis and drops no
conclusion, while the predicate becomes applicable where the two readings of a level agree only
up to a canonical isomorphism — as they do when the legs are chosen fibre products.

It is named rather than written out because of a cost that recurs in this development:
written out at a *concrete* system — one whose `D` is a projection of a large structure literal —
the telescope mentions `D.I`, `D.C i` and `D.u a` some thirty times, and the elaborator goes
through that projection at each occurrence, exhausting the heartbeat budget in the SIGNATURE
before any proof runs. The same rule is recorded on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem` and on
`Stacks.WeakSites.ColimitGlobalSections.GlobalSectionsIsColimit`. Here `D`, `v` and `F` are
variables and nothing unfolds. -/
def RestrictionIsColimit (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (v : ∀ i, D.C i ⥤ E)
    (hv : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ v i ≅ v j) (F : Sheaf J (Type w)) : Prop :=
  ∀ (H : Sheaf J (Type w))
    (ψ : ∀ {i j : D.I} (a : j ⟶ i),
      (v i).op ⋙ F.obj ⟶ (D.u a).op ⋙ ((v j).op ⋙ F.obj)),
    (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : F.obj.obj (op ((v i).obj V))),
        (ψ a).app (op V) x = F.obj.map ((hv a).hom.app V).op x) →
    ∀ (g : ∀ i, (v i).op ⋙ F.obj ⟶ (v i).op ⋙ H.obj),
    (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i) (x : F.obj.obj (op ((v i).obj V))),
        (g i).app (op V) x =
          H.obj.map ((hv a).inv.app V).op
            ((g j).app (op ((D.u a).obj V)) ((ψ a).app (op V) x))) →
    ∃! h : F ⟶ H, ∀ (i : D.I) (V : D.C i) (x : F.obj.obj (op ((v i).obj V))),
      (g i).app (op V) x = h.hom.app (op ((v i).obj V)) x

/-- **The four site inputs of Stacks 09YL at a family of functors `u i`, bundled.** The objects
and the morphisms of `C` descend to a level, two morphisms of a level agreeing over `C` agree at a
further level, and the coverings of `K` are the images of the finite coverings of the levels.

Bundling them is what lets the cost of instantiating them at a concrete system be paid in a
declaration of its own: every one of them matches its geometric counterpart syntactically, but the
budget is per declaration, and the four together with the rest of the telescope of
`descent_along_restriction` exceed it. -/
structure ColimitSiteInputs (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j) : Prop where
  /-- Every object of `C` descends to a level. -/
  hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X
  /-- Every morphism between objects descended from one level descends after lowering the
  level. -/
  hhom : ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
      (u j).map g =
        eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm
  /-- Two morphisms of a level that agree over `C` agree at a further level. -/
  hhom_inj : ∀ (i : D.I) (X Y : D.C i) (g₁ g₂ : X ⟶ Y),
    (u i).map g₁ = (u i).map g₂ → ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂
  /-- The coverings of `K` are exactly the images of the finite coverings of the levels. -/
  hK : ∀ (X : C) (R : Presieve X), R ∈ K X ↔
    ∃ (i : D.I) (Y : D.C i) (h : (u i).obj Y = X) (S : Presieve Y),
      S ∈ (D.J i).toPrecoverage Y ∧ S ∈ Precoverage.finite (D.C i) Y ∧ R = h ▸ S.map (u i)

/-- `descent_along_restriction` read as the predicate `RestrictionIsColimit`, with its four site
inputs taken as one bundle. This is the form a geometric instantiation applies: the bundle is
built in its own declaration, and nothing here costs the elaborator anything, `D`, `u` and `F`
being variables. -/
theorem restrictionIsColimit_of_inputs (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hin : ColimitSiteInputs K D u hu)
    [(Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).Full]
    [(Λ.sheafPushforwardContinuous (Type w) K.toGrothendieck J).Faithful]
    (F : Sheaf J (Type w)) :
    RestrictionIsColimit J D (fun i => u i ⋙ Λ) (compTransitionIso Λ D u hu) F := by
  intro H ψ hψ g hg
  refine descent_along_restriction K J Λ D u hu hin.hobj hin.hhom hin.hhom_inj hin.hK F H ψ
    (fun a V x => ?_) g (fun a V x => ?_)
  · rw [hψ a V x, map_op_compTransitionIso_hom_app]
  · rw [hg a V x, map_op_compTransitionIso_inv_app]

end CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

/-! ### The small étale site of the limit

The two crossings, carried out for the system of sites of Stacks 0EYL. -/

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- **The composite of the two crossings**: from the raised small affine étale site of the limit
`X = lim X_i` to the small étale site of `X`. It is `AsSmall.down` followed by the inclusion of
Stacks 04HR, so restriction along it is restriction along both at once. -/
noncomputable def limitToSmallEtale :
    limitSite D c B hX ⥤ AlgebraicGeometry.SmallEtale B c.pt hX :=
  AsSmall.down ⋙ AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX

/-- **The functor from a level of the system of sites of Stacks 0EYL to the small étale site of
the limit.** This is the functor the statements below restrict along: `toLimitSmall i` lands in
the raised site, and `limitToSmallEtale` carries it to the small étale site of `X`. -/
noncomputable def levelFunctor (i : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C i ⥤ AlgebraicGeometry.SmallEtale B c.pt hX :=
  toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX

/-- **The cocone identity of Stacks 09YL** on the small étale site of the limit: the functors
`levelFunctor` are compatible with the transition functors of the system. -/
theorem levelFunctor_transition {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    (sys D c B hD hX hc).u a ⋙ levelFunctor D c B hD hX hc i =
      levelFunctor D c B hD hX hc j := by
  rw [levelFunctor, levelFunctor, ← Functor.assoc, toLimitSmall_transition]

/-- The composite crossing is a morphism of sites, from the étale coverings of the raised site of
the limit to the small étale topology of the limit. The `AsSmall` half is
`CategoryTheory.AsSmall.isContinuous_down`, the 04HR half comes from the dense-subsite
instance. -/
instance isContinuous_limitToSmallEtale :
    (limitToSmallEtale D c B hX).IsContinuous (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX) :=
  have _h1 : (AsSmall.down : limitSite D c B hX ⥤ _).IsContinuous
      (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) :=
    AsSmall.isContinuous_down (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
  Functor.isContinuous_comp (AsSmall.down)
    (AlgebraicGeometry.SmallAffineEtale.inclusion B c.pt hX) _
    (AlgebraicGeometry.SmallAffineEtale.topology B c.pt hX) _

/-- Restriction along the composite crossing is full: it is the composite of the Stacks 04HR
equivalence on sheaves of sets (`AlgebraicGeometry.SmallAffineEtale.sheafEquiv`) with the
`AsSmall` raising, each of which is full. -/
instance full_limitRestriction :
    ((limitToSmallEtale D c B hX).sheafPushforwardContinuous (Type (max u v + 1))
      (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)).Full :=
  inferInstanceAs
    (((AlgebraicGeometry.SmallAffineEtale.sheafEquiv B c.pt hX).inverse ⋙
      AsSmall.sheafRaise (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
        (Type (max u v + 1))).Full)

/-- Restriction along the composite crossing is faithful, for the same reason. -/
instance faithful_limitRestriction :
    ((limitToSmallEtale D c B hX).sheafPushforwardContinuous (Type (max u v + 1))
      (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)).Faithful :=
  inferInstanceAs
    (((AlgebraicGeometry.SmallAffineEtale.sheafEquiv B c.pt hX).inverse ⋙
      AsSmall.sheafRaise (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
        (Type (max u v + 1))).Faithful)

/-- **Restriction of sheaves of sets along the composite crossing.** This is the functor that
carries a sheaf on the small étale site of the limit to a sheaf on the site Stacks 09YL exhibits
as a colimit, and by the two instances above it is fully faithful. -/
noncomputable def raiseFunctor :
    Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)) ⥤
      Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)) :=
  (limitToSmallEtale D c B hX).sheafPushforwardContinuous (Type (max u v + 1))
    (limitSitePrecoverage D c B hX).toGrothendieck
    (AlgebraicGeometry.SmallEtale.topology B c.pt hX)

/-- A sheaf of sets on the small étale site of the limit, read on the raised site. -/
noncomputable def raisedSheaf
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1))) :
    Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)) :=
  (raiseFunctor D c B hX).obj F

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Raising a sheaf does not change its sections: the underlying presheaf is restriction along the
composite crossing, on the nose. -/
theorem raisedSheaf_obj
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1))) :
    (raisedSheaf D c B hX F).obj = (limitToSmallEtale D c B hX).op ⋙ F.obj :=
  rfl

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] in
/-- Raising a morphism of sheaves acts on components by reindexing along the crossing. -/
theorem raiseFunctor_map_hom_app
    {F H : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1))}
    (h : F ⟶ H) (Z : limitSite D c B hX) :
    ((raiseFunctor D c B hX).map h).hom.app (op Z) =
      h.hom.app (op ((limitToSmallEtale D c B hX).obj Z)) :=
  rfl

/-- **The restriction of a sheaf on the small étale site of the limit to a level** of the system
of sites of Stacks 0EYL. This is the object `p_{i,*}F` of Stacks 0EYN read on the level: the
sections over a level object `V` are the sections of `F` over the image of `V` in the small étale
site of the limit. -/
noncomputable def levelRestrict
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (i : (sys D c B hD hX hc).I) :
    ((sys D c B hD hX hc).C i)ᵒᵖ ⥤ Type (max u v + 1) :=
  (levelFunctor D c B hD hX hc i).op ⋙ F.obj

/-- The level restriction is what the machinery of Stacks 09YN consumes: restriction along the
machinery's own functor `toLimitSmall i` of the raised sheaf. The identification is definitional,
which is the whole point of the two crossings being restrictions. -/
theorem levelRestrict_eq_raised
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (i : (sys D c B hD hX hc).I) :
    levelRestrict D c B hD hX hc F i =
      (toLimitSmall D c B hD hX hc i).op ⋙ (raisedSheaf D c B hX F).obj :=
  rfl

/-- Sections of the level restriction over a level object are sections of `F` over its image. -/
theorem levelRestrict_obj
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (i : (sys D c B hD hX hc).I) (V : (sys D c B hD hX hc).C i) :
    (levelRestrict D c B hD hX hc F i).obj (op V) =
      F.obj.obj (op ((levelFunctor D c B hD hX hc i).obj V)) :=
  rfl

/-- **The four site inputs of Stacks 09YL for the system of sites of [Stacks, Tag 0EYL]**, on the
raised small affine étale site of the limit, bundled as
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.ColimitSiteInputs`. The three
descent clauses are `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends` and
`toLimitSmall_hom_eventually_eq`; the description of the coverings is
`mem_limitSitePrecoverage_iff`.

The last field is proved by `rw` rather than by naming that theorem. Its final clause is a
transport `R = h ▸ S.map (toLimitSmall …)`, and the motive of the `▸` in the field's type -- the
one elaborated against the machinery's variable `u` -- is definitionally but not syntactically the
motive the theorem's own statement carries; deciding them is a heartbeat timeout, while rewriting
the goal with the equivalence closes it outright. -/
theorem colimitSiteInputs_toLimitSmall :
    InverseSystemOfFiniteSites.ColimitSiteInputs (limitSitePrecoverage D c B hX)
      (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) where
  hobj := toLimitSmall_obj_descends D c B hD hX hc
  hhom := toLimitSmall_hom_descends D c B hD hX hc
  hhom_inj := toLimitSmall_hom_eventually_eq D c B hD hX hc
  hK Z R := by rw [mem_limitSitePrecoverage_iff D c B hD hX hc]

/-- **Stacks 0EYN, second half, on the small étale site of a limit of schemes.** Let `(X_i)` be
an inverse system of schemes with affine transition morphisms over a nonempty directed index, all
of them objects of a big étale site `B`, let `X = lim X_i`, and let `F` be a sheaf of sets on the
small étale site of `X`. Then

`F = colim_i p_i^{-1} p_{i,*} F`,

in the form the inverse-system machinery proves it: every family of maps out of the restrictions
of `F` to the levels of the system of sites of [Stacks, Tag 0EYL], compatible with the canonical
transition maps, is the restriction of a **unique** map of sheaves out of `F`. Those restrictions
are the `p_{i,*}F` read on the levels — they are `levelRestrict`, whose sections over a level
object are the sections of `F` over its image in the site of the limit (`levelRestrict_obj`, an
`rfl`), and that image is the base change of the level object along `p_i`.

This is the geometric instantiation of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction` at
`Λ = limitToSmallEtale`: the five site inputs of [Stacks, Tag 09YP] for the raised site are
`toLimitSmall_transition`, `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`,
`toLimitSmall_hom_eventually_eq` and `mem_limitSitePrecoverage_iff`, and the two instances making
restriction along the composite crossing fully faithful are `full_limitRestriction` and
`faithful_limitRestriction`.

**Why the conclusion is the named predicate.** Written out, the telescope mentions
`(sys D c B hD hX hc).I`, `.C i` and `.u a` some thirty times and exceeds the heartbeat budget in
the signature; the failure is a `(deterministic) timeout at isDefEq`
inside the compatibility hypothesis of the family `g`, before any proof runs. The docstring of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit` records the
rule and the three other places in this development where it was needed.

**Why `hK` is supplied by `rw` and not as a term.** `mem_limitSitePrecoverage_iff` states exactly
the required equivalence, but its last clause is a transport `R = h ▸ S.map (toLimitSmall …)`
whose motive was elaborated against the concrete functor, while the motive the machinery's
hypothesis carries is the one elaborated against its variable `u`. The two are definitionally
equal and deciding them is another heartbeat timeout; rewriting the goal with the equivalence
closes it outright instead.

Part (1) of the tag, that the `p_{i,*}F` carry canonical maps making them a system of sheaves in
the sense of [Stacks, Tag 0EZL], is `Stacks.EtaleCohomology.directImageSystem`, which states it on
Mathlib's small étale site; that declaration and this one are the covering set of Tag 0EYN. -/
@[stacks 0EYN "part (2): `F = colim_i p_i^{-1}p_{i,*}F`, on the site of Stacks 021B"]
theorem restrictionIsColimit_limitToSmallEtale
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1))) :
    InverseSystemOfFiniteSites.RestrictionIsColimit
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (sys D c B hD hX hc)
      (fun i => toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX)
      (InverseSystemOfFiniteSites.compTransitionIso (limitToSmallEtale D c B hX)
        (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)) F :=
  InverseSystemOfFiniteSites.restrictionIsColimit_of_inputs
    (limitSitePrecoverage D c B hX) (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
    (limitToSmallEtale D c B hX) (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) (colimitSiteInputs_toLimitSmall D c B hD hX hc) F

end Stacks.EtaleCohomology.AffineLimitCohomology
