module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PairToCrystal

/-!
# The crystal condition for the assignment `T ↦ M ⊗_{D,f} B` of [Stacks, Tag 07JH]

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] builds, out of a pair `(M, ∇)`, the
assignment sending an affine object `(U, T, δ)` of `Cris(X/S)` with `T = Spec(B)` to
`ℱ_T = M ⊗_{D,f} B`, and asserts of it:

> If `a : (U', T', δ') → (U, T, δ)` is a morphism of affine objects of `Cris(X/S)`, then choosing
> `f' = f ∘ a` it is clear that there exists a canonical isomorphism `a^*ℱ_T → ℱ_{T'}`.

`Crystalline.pointedRestriction` of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean` is that canonical map.  This module
proves that it **is** an isomorphism — the crystal condition proper for the assignment — in the
form that does not require the base change `a^*ℱ_T = B' ⊗_B ℱ_T` to be built: that
`Crystalline.pointedSections M T'` together with the restriction map has the universal property of
that base change.

## Why this is unconditional

The module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean` records this as not proved and adds
that "over the pointed site that is flatness-free only when `u` is an isomorphism".  That caveat
belongs to the comparison with the pullback of *sheaves* of modules, where sheafification and
quasi-coherence enter.  At the level of the modules themselves no flatness is involved and no
hypothesis at all is needed, because `ℱ_T` is by construction a base change along the chosen map:
`ℱ_T = TwistedScalars f ⊗_D M`, and

`B' ⊗_B (B ⊗_D M) = B' ⊗_D M`

is the cancellation of two successive base changes, which is an isomorphism for any ring maps.
The pointed site is exactly where this is visible, the chosen maps composing on the nose by
`Crystalline.pointedHomRingHom_pointRingHom`.

The universal property is used rather than the tensor product `B' ⊗_B ℱ_T` because `B'` is a
`B`-algebra only along the chosen map of the morphism, so forming that tensor product means a
second `Crystalline.TwistedScalars` layer; the universal property characterises the base change
and is stated with the modules already present.

## Main definitions

* `Crystalline.pointedUnitSection` — the `f`-semilinear map `m ↦ 1 ⊗ m` into the sections over a
  pointed object, the unit of the base change `ℱ_T = M ⊗_{D,f} B`.
* `Crystalline.pointedRestrictionUnitDatum` — an `a`-semilinear map out of `ℱ_T` read on the unit
  sections, which is the `f ∘ a`-semilinear datum the extension is built from.

## Main results

* `Crystalline.span_range_pointedRestriction_eq_top` — **the surjectivity half**: the image of the
  restriction map generates `ℱ_{T'}` over `B'`.  So `a^*ℱ_T → ℱ_{T'}` is surjective, with no
  hypotheses.
* `Crystalline.existsUnique_pointedRestriction` — **the crystal condition**: for every `B'`-module
  `N` and every `a`-semilinear map out of `ℱ_T`, there is a unique `B'`-linear map out of
  `ℱ_{T'}` restricting to it along the restriction map.  This is the universal property of
  `a^*ℱ_T`, so the canonical map `a^*ℱ_T → ℱ_{T'}` is an isomorphism.
* `Crystalline.pointedRestriction_injective_of_comp` — the uniqueness half on its own: two
  `B'`-linear maps out of `ℱ_{T'}` that agree after the restriction map are equal.
* `Crystalline.semilinearBaseChange_pointedRestrictionUnitDatum` — the existence half on its own:
  the extension really does restrict to the map it was built from.
* `Crystalline.pointedRestriction_pointedUnitSection` — the restriction map carries the unit of
  `ℱ_T` to the unit of `ℱ_{T'}`, which is the source's `f' = f ∘ a` read on the modules.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
The tag is an equivalence of categories, and this module is the crystal condition for one object
assignment.  Two of the three verifications the source omits are elsewhere: independence of the
restriction maps from the chosen pointing is
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorRestrictionIndependence.lean`, and the cocycle
and `c_{f,f} = 1` are in
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedTaylorComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean`.

What this module does **not** do is pass from the pointed affine site to `Cris(X/S)`.  The crystal
condition proved here is the one for the `D`-module–valued functor on `Under Dt`; it is carried
over to the unpointed algebraic site `CRIS(C/A)` in
`StacksFrontier/AlgebraicGeometry/Crystalline/PointedDescent.lean`, as
`Crystalline.PointedComparisonSystem.existsUnique_descendedRestrict`, and the sheaf-level
condition on `Cris(X/S)` needs beyond that the identification of the affine site with the small
site and the quasi-coherence clause, both recorded in the "What is and is not proved" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean`.  Nor are the four conditions of the
pair used: as that module records, the object assignment and so this condition exist for a pair
with no conditions at all.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u uI v w w'

namespace Crystalline

section CrystalCondition

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  (M : Type w) [AddCommGroup M] [Module Dt.ring.carrier M]

/-- **The unit of the base change `ℱ_T = M ⊗_{D,f} B`**: the `f`-semilinear map `m ↦ 1 ⊗ m` into
the sections over a pointed object.  Every `B`-linear map out of `ℱ_T` is determined by its
composite with it, by `Crystalline.baseChange_ext`, and that is what makes the universal property
below an identification. -/
noncomputable def pointedUnitSection (T : PointedThickening Dt) :
    M →ₛₗ[pointRingHom T] pointedSections M T where
  toFun m := (1 : TwistedScalars (pointRingHom T)) ⊗ₜ[Dt.ring.carrier] m
  map_add' m m' := TensorProduct.tmul_add _ m m'
  map_smul' a m := by
    change (1 : TwistedScalars (pointRingHom T)) ⊗ₜ[Dt.ring.carrier] (a • m) =
      pointRingHom T a • ((1 : TwistedScalars (pointRingHom T)) ⊗ₜ[Dt.ring.carrier] m)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    refine congrArg (fun b ↦ b ⊗ₜ[Dt.ring.carrier] m) ?_
    change a • (1 : TwistedScalars (pointRingHom T)) =
      pointRingHom T a • (1 : TwistedScalars (pointRingHom T))
    exact (TwistedScalars.smul_val (f := pointRingHom T) a 1).trans
      (TwistedScalars.val_smul (f := pointRingHom T) (pointRingHom T a) 1).symm

/-- The unit section `pointedUnitSection M T` sends `m` to `1 ⊗ m`. -/
@[simp] theorem pointedUnitSection_apply (T : PointedThickening Dt) (m : M) :
    pointedUnitSection M T m =
      (1 : TwistedScalars (pointRingHom T)) ⊗ₜ[Dt.ring.carrier] m := rfl

/-- **A generator of `ℱ_T` is a `B`-multiple of a unit section.**  This is
`Crystalline.tmul_eq_smul_one_tmul` read on the sections over a pointed object. -/
theorem pointedSections_tmul_eq_smul (T : PointedThickening Dt)
    (b : TwistedScalars (pointRingHom T)) (m : M) :
    b ⊗ₜ[Dt.ring.carrier] m = b.val • pointedUnitSection M T m :=
  tmul_eq_smul_one_tmul b m

/-- **The restriction map carries the unit of `ℱ_T` to the unit of `ℱ_{T'}`.**  This is the
source's choice `f' = f ∘ a` read on the modules: the generator `1 ⊗ m` is the same on both
sides, which is why the restriction map exists at all. -/
@[simp] theorem pointedRestriction_pointedUnitSection {T T' : PointedThickening Dt}
    (u : T ⟶ T') (m : M) :
    pointedRestriction M u (pointedUnitSection M T m) = pointedUnitSection M T' m := by
  rw [pointedUnitSection_apply, pointedRestriction_tmul]
  refine congrArg (fun b ↦ b ⊗ₜ[Dt.ring.carrier] m) ?_
  have h : (pointedScalarsMap u (1 : TwistedScalars (pointRingHom T))).val =
      (1 : TwistedScalars (pointRingHom T')).val := by
    rw [pointedScalarsMap_val, TwistedScalars.val_one, TwistedScalars.val_one, map_one]
  exact h

/-- **The surjectivity half of the crystal condition**: the image of the restriction map generates
`ℱ_{T'}` as a `B'`-module.

Every generator `b' ⊗ m` of `ℱ_{T'}` is `b'` times the unit section, which is the restriction of
the unit section of `ℱ_T` by `Crystalline.pointedRestriction_pointedUnitSection`.  So the
canonical map `a^*ℱ_T → ℱ_{T'}` is surjective, with no hypotheses — in particular with no
flatness. -/
theorem span_range_pointedRestriction_eq_top {T T' : PointedThickening Dt} (u : T ⟶ T') :
    Submodule.span T'.right.ring.carrier
        (Set.range (pointedRestriction M u)) = ⊤ := by
  have key : ∀ z : pointedSections M T', z ∈ Submodule.span T'.right.ring.carrier
      (Set.range (pointedRestriction M u)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul b m =>
        rw [pointedSections_tmul_eq_smul M T' b m, ← pointedRestriction_pointedUnitSection M u m]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add z z' hz hz' => exact Submodule.add_mem _ hz hz'
  exact top_unique fun z _ ↦ key z

/-- **The uniqueness half of the crystal condition**: two `B'`-linear maps out of `ℱ_{T'}` that
agree after the restriction map are equal.

By `Crystalline.baseChange_ext` it is enough that they agree on the unit sections of `ℱ_{T'}`, and
those are the restrictions of the unit sections of `ℱ_T`. -/
theorem pointedRestriction_injective_of_comp {T T' : PointedThickening Dt} (u : T ⟶ T')
    {N : Type w'} [AddCommGroup N] [Module T'.right.ring.carrier N]
    {c c' : pointedSections M T' →ₗ[T'.right.ring.carrier] N}
    (h : ∀ z : pointedSections M T, c (pointedRestriction M u z) =
      c' (pointedRestriction M u z)) : c = c' := by
  refine baseChange_ext fun m ↦ ?_
  have hm := h (pointedUnitSection M T m)
  rw [pointedRestriction_pointedUnitSection] at hm
  exact hm

/-- **The `f ∘ a`-semilinear datum of the universal property.**  An `a`-semilinear map out of
`ℱ_T` restricted to the unit sections is `f ∘ a`-semilinear, the chosen maps composing on the nose
by `Crystalline.pointedHomRingHom_pointRingHom`.  This is the datum
`Crystalline.semilinearBaseChange` turns into the `B'`-linear map out of `ℱ_{T'}`. -/
noncomputable def pointedRestrictionUnitDatum {T T' : PointedThickening Dt} (u : T ⟶ T')
    {N : Type w'} [AddCommGroup N] [Module T'.right.ring.carrier N]
    (s : pointedSections M T →ₛₗ[pointedHomRingHom u] N) : M →ₛₗ[pointRingHom T'] N where
  toFun m := s (pointedUnitSection M T m)
  map_add' m m' := by
    show s (pointedUnitSection M T (m + m')) = _
    rw [map_add, map_add]
  map_smul' a m := by
    change s (pointedUnitSection M T (a • m)) = pointRingHom T' a • s (pointedUnitSection M T m)
    rw [map_smulₛₗ (pointedUnitSection M T), map_smulₛₗ s, pointedHomRingHom_pointRingHom]

/-- The datum `pointedRestrictionUnitDatum M u s` sends `m` to `s (1 ⊗ m)`. -/
@[simp] theorem pointedRestrictionUnitDatum_apply {T T' : PointedThickening Dt} (u : T ⟶ T')
    {N : Type w'} [AddCommGroup N] [Module T'.right.ring.carrier N]
    (s : pointedSections M T →ₛₗ[pointedHomRingHom u] N) (m : M) :
    pointedRestrictionUnitDatum M u s m = s (pointedUnitSection M T m) := rfl

/-- **The extension of an `a`-semilinear map along the restriction map.**  The `B'`-linear map out
of `ℱ_{T'}` built from `Crystalline.pointedRestrictionUnitDatum` restricts to the map it came
from: this is the existence half of the crystal condition.

On a generator `b ⊗ m` both sides are `a(b) · s(1 ⊗ m)`, the left by
`Crystalline.semilinearBaseChange_tmul` and `Crystalline.pointedScalarsMap_val`, the right by
semilinearity of `s` applied to `b ⊗ m = b · (1 ⊗ m)`. -/
theorem semilinearBaseChange_pointedRestrictionUnitDatum {T T' : PointedThickening Dt}
    (u : T ⟶ T') {N : Type w'} [AddCommGroup N] [Module T'.right.ring.carrier N]
    (s : pointedSections M T →ₛₗ[pointedHomRingHom u] N) (z : pointedSections M T) :
    semilinearBaseChange (pointedRestrictionUnitDatum M u s) (pointedRestriction M u z) = s z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b m =>
      rw [pointedRestriction_tmul, semilinearBaseChange_tmul, pointedScalarsMap_val,
        pointedSections_tmul_eq_smul M T b m, map_smulₛₗ s]
      rfl
  | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']

/-- **The crystal condition for the assignment `T ↦ M ⊗_{D,f} B` of [Stacks, Tag 07JH].**

For every `B'`-module `N` and every `a`-semilinear map `s : ℱ_T → N` there is exactly one
`B'`-linear map `c : ℱ_{T'} → N` with `c ∘ a = s`.  That is the universal property of the base
change `a^*ℱ_T = B' ⊗_B ℱ_T`, so the canonical map `a^*ℱ_T → ℱ_{T'}` of the source's proof **is an
isomorphism**: the source's "it is clear that there exists a canonical isomorphism
`a^*ℱ_T → ℱ_{T'}`", proved.

There are no hypotheses, and in particular no flatness: `ℱ_T` is itself a base change along the
chosen map `f`, and `ℱ_{T'}` is the base change along `f ∘ a`, so the statement is the
cancellation of two successive base changes.  Existence is
`Crystalline.semilinearBaseChange_pointedRestrictionUnitDatum` and uniqueness is
`Crystalline.pointedRestriction_injective_of_comp`. -/
theorem existsUnique_pointedRestriction {T T' : PointedThickening Dt} (u : T ⟶ T')
    {N : Type w'} [AddCommGroup N] [Module T'.right.ring.carrier N]
    (s : pointedSections M T →ₛₗ[pointedHomRingHom u] N) :
    ∃! c : pointedSections M T' →ₗ[T'.right.ring.carrier] N,
      ∀ z : pointedSections M T, c (pointedRestriction M u z) = s z :=
  ⟨semilinearBaseChange (pointedRestrictionUnitDatum M u s),
    semilinearBaseChange_pointedRestrictionUnitDatum M u s,
    fun c hc ↦ pointedRestriction_injective_of_comp M u fun z ↦ by
      rw [hc z, semilinearBaseChange_pointedRestrictionUnitDatum]⟩

end CrystalCondition

end Crystalline

end
