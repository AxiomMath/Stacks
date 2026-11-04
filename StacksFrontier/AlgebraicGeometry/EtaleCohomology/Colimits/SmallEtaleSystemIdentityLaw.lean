module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSitesSystems

/-!
# The identity law, and why a Tag 0EZL system does not transport onto the levels of Tag 0EYL

The statements of [Stacks, Tag 09YQ] on the *affine* sites — among them
`Stacks.EtaleCohomology.QcqsLimitCohomology.vanishesOnObjects_colimit_of_pointwise_injective`,
`QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation` and
`Stacks.EtaleCohomology.AffineLimitCohomology.etaleCohomologyColimit_isColimit_of_affine` — take
their system of coefficients as an
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` on the levels
of [Stacks, Tag 0EYL], and the presentation hypothesis
`Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation` for it. The statements of
[Stacks, Tag 09YQ] on *Mathlib's* small étale sites take theirs as a
`Stacks.EtaleCohomology.EtaleSheafSystem` — [Stacks, Tag 0EZL] — with the presentation
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`.

**The two notions of system are not related by a levelwise transport, and this file measures why.**
`AbelianSheafSystem` carries a field `map_id`, which in the direct-image vocabulary says that the
transition along an identity arrow is the canonical transport
(`Stacks.WeakSites.ColimitSiteCohomology.transition_id_eqToHom`) and in particular an
isomorphism. `EtaleSheafSystem` carries no such field: following the source, [Stacks, Tag 0EZL]
imposes only the cocycle condition, so the identity transition is merely an *idempotent*
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem`). The gap is not an
artefact of the bookkeeping: there is no strictness field to appeal to on Mathlib's small étale
sites, base change along `𝟙 X` being the functor `U ↦ U ×_X X` rather than the identity functor.

What this file adds is a *witness* that the gap is real in the presence of a colimit
presentation, so that the discrepancy cannot be argued away from the presentation hypothesis:
for an arbitrary family `A` of abelian sheaves on the small étale sites of the levels, the system
with all transitions zero carries a colimit presentation, by the zero sheaf on the limit with the
zero legs.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.zeroTransitionSystem` — the system of
  [Stacks, Tag 0EZL] with prescribed sheaves at the levels and **all transitions zero**. The
  cocycle condition holds because both sides are zero; there is no identity law to violate.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.zeroTransitionPresentedSystem` — that system
  as a `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` for
  `IsColimitPresentation`.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.isIso_transition_id` — **the identity transition of an
  `AbelianSheafSystem` is an isomorphism.**
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_zeroTransitionSystem` —
  **the zero sheaf on the limit, with the zero legs, presents the colimit of the
  zero-transition system**, whatever the sheaves at the levels are.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_zeroTransitionSystem` —
  its transitions, read as maps out of `Stacks.EtaleCohomology.etaleAbelianInverseImage`, are
  zero.
* `id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem` — **an identity transition of
  that system is invertible only if the sheaf at the level has zero identity**, i.e. is a zero
  object.

## What this measures, and what it leaves

Put together: a levelwise transport of a presented system `E` onto the levels of
[Stacks, Tag 0EYL] — one whose sheaf at a level is the restriction of `E.sys.obj i`, which is
what the `hF : ∀ j, Injective (F.obj j)` hypothesis of the affine-site statements needs —
would have to carry `E.sys`'s identity transition to the identity transition of an
`AbelianSheafSystem`. By `isIso_transition_id` the latter is invertible; by
`isColimitPresentation_zeroTransitionSystem` and
`id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem` the former can be zero on a
*nonzero* sheaf while the presentation hypothesis holds. So no such transport exists, and the
passage between the two presentation predicates is not the two sheaf-category equivalences plus a
matching of transition data.

**What the passage needs instead.** The identity transition is an idempotent, and only its
*image* carries an identity law, so the repair is to split it and transport the split system.
It can be split on the *inverse images* `f_i^{-1}E.sys.obj i` — but these are sheaves on the
limit, so `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemDiagramIdem` is an
idempotent on `f_i^{-1}E.sys.obj i` and not on `E.sys.obj i`, and the system it splits is not a
system on the levels.

**And the cheapest place to split is the 0EYL side, not Mathlib's.** Splitting on `E.sys.obj i`
itself would need the comparison of base change along `𝟙 X_i` with the identity functor of the
small étale site, together with the unit coherence of the cocycle condition against it; neither
is in this library. On the levels of [Stacks, Tag 0EYL] none of that arises:
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` carries `id_map` and `comp` as
*equalities* of functors, so the restriction-form transition datum of an arbitrary system at an
identity arrow is a genuine endomorphism of a sheaf on the level up to `CategoryTheory.eqToHom`,
the cocycle law makes it idempotent by `eqToHom` algebra alone, and the sheaf category on a level
is abelian, so the idempotent splits.

**That construction is available.**
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` is
direct-image transition data on the levels subject to the cocycle law alone,
`...AbelianCocycleSystem.idem_idem` says its datum at an identity arrow is idempotent,
`...AbelianCocycleSystem.split` is the
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` obtained by
splitting those idempotents, and `...AbelianCocycleSystem.isColimitPresentation_split` carries a
whole colimit presentation of the unsplit data to one of the split system — not only a compatible
family, which is
`Stacks.WeakSites.ColimitSiteCohomology.isCompatible_split`. What remains for the passage is
the site crossing, which has to produce cocycle data on the levels of [Stacks, Tag 0EYL] out of
`E.sys` and a presentation of it.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Sites.InverseSystem

namespace Stacks.WeakSites.ColimitSiteCohomology

universe wD uD vD tD

/-- **The identity transition of a system of abelian sheaves on an inverse system of sites is an
isomorphism.** It is the canonical transport along the strictness field
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.id_map`, by
`Stacks.WeakSites.ColimitSiteCohomology.transition_id_eqToHom`.

This is the half of the `InverseSystemOfFiniteSites.AbelianSheafSystem.map_id` field that a
system of abelian sheaves on an inverse system of *schemes* ([Stacks, Tag 0EZL]) does not have;
see the module docstring. -/
theorem isIso_transition_id (D : InverseSystemOfFiniteSites.{vD, uD, wD})
    (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{vD, uD, wD, tD} D) (i : D.I) :
    IsIso (transition.{vD, uD, wD, tD} D F (𝟙 i)) := by
  rw [transition_id_eqToHom.{vD, uD, wD, tD}]
  infer_instance

end Stacks.WeakSites.ColimitSiteCohomology

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- **The system of [Stacks, Tag 0EZL] with prescribed sheaves and all transitions zero.** The
cocycle condition holds because both of its sides are zero, and the structure imposes no identity
law, so this is a system whatever the sheaves `A i` are.

With `A i = 0` it is
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.trivialSystem`; the point of the general form is
that the sheaves at the levels are arbitrary — in particular nonzero, and in particular
injective — while the transitions are not invertible. See the module docstring. -/
def zeroTransitionSystem
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) :
    EtaleSheafSystem D AddCommGrpCat.{u + 1} where
  obj := A
  map _ := 0
  map_comp _ _ := by simp

/-- The sheaf of `zeroTransitionSystem A` at the level `i` is `A i`. -/
@[simp]
theorem zeroTransitionSystem_obj
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) (i : Iᵒᵖ) :
    (zeroTransitionSystem A).obj i = A i := rfl

/-- Every transition of `zeroTransitionSystem A` is zero. -/
@[simp]
theorem zeroTransitionSystem_map
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) : (zeroTransitionSystem A).map a = 0 := rfl

variable [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]

/-- The transitions of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.zeroTransitionSystem`,
read as maps out of `Stacks.EtaleCohomology.etaleAbelianInverseImage` rather than out of
`Stacks.EtaleCohomology.systemPullback`, are zero. -/
@[simp]
theorem systemTransitionMap_zeroTransitionSystem
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) : systemTransitionMap (zeroTransitionSystem A) a = 0 := by
  rw [systemTransitionMap, zeroTransitionSystem_map, comp_zero]

/-- **The zero sheaf on the limit, with the zero legs, presents the colimit of the
zero-transition system** — whatever the sheaves at the levels are.

Compatibility is immediate, both sides being zero. For the universal property, the compatibility
of a family `τ` at an *identity* arrow of the index already forces `τ` to vanish, the transition
there being zero; and a map out of a zero object is unique. -/
theorem isColimitPresentation_zeroTransitionSystem
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}] :
    IsColimitPresentation (c := c) (zeroTransitionSystem A) 0 (fun _ => 0) where
  compatible := fun _ => by rw [comp_zero, comp_zero]
  existsUnique_desc H τ hτ := by
    have hτ0 (i : Iᵒᵖ) : τ i = 0 := by
      simpa only [systemTransitionMap_zeroTransitionSystem, Functor.map_zero, zero_comp,
        comp_zero] using (hτ (𝟙 i)).symm
    exact ⟨0, fun i => by rw [hτ0 i, zero_comp], fun y _ => (isZero_zero _).eq_of_src _ _⟩

/-- **A nonzero system with a colimit presentation whose identity transitions are all zero.**
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.zeroTransitionSystem`, presented by the zero
sheaf on the limit with the zero legs, read as a
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` through
`presentedSystemOfIsColimitPresentation`.

Unlike `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.trivialPresentedSystem` the sheaves at
the levels are arbitrary: the quantifier `∀ E : PresentedSystem IsColimitPresentation` of
`isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` reaches systems whose identity
transition is not invertible. -/
def zeroTransitionPresentedSystem
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) (c : Cone D)
    [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})] :
    PresentedSystem (c := c) IsColimitPresentation :=
  presentedSystemOfIsColimitPresentation (zeroTransitionSystem A) 0 (fun _ => 0)
    (isColimitPresentation_zeroTransitionSystem A c)

/-- **The identity transition of the zero-transition system is invertible only on a zero sheaf.**
If the transition of `zeroTransitionSystem A` at an identity arrow of the index is an
isomorphism, then the identity of `A i` is zero, i.e. `A i` is a zero object.

Against `Stacks.WeakSites.ColimitSiteCohomology.isIso_transition_id`, which says that the
identity transition of an
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` *is* an
isomorphism, this is the obstruction the module docstring records: a presented system of
[Stacks, Tag 0EZL] with a nonzero sheaf at a level does not transport levelwise to a system of
abelian sheaves on the levels of [Stacks, Tag 0EYL]. -/
theorem id_eq_zero_of_isIso_systemTransitionMap_zeroTransitionSystem
    (A : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) (i : Iᵒᵖ)
    (h : IsIso (systemTransitionMap (zeroTransitionSystem A) (𝟙 i))) : 𝟙 (A i) = 0 := by
  rw [systemTransitionMap_zeroTransitionSystem] at h
  exact (IsIso.inv_hom_id (0 : (etaleAbelianInverseImage.{u, u + 1} (D.map (𝟙 i))).obj
    ((zeroTransitionSystem A).obj i) ⟶ (zeroTransitionSystem A).obj i)).symm.trans comp_zero

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
