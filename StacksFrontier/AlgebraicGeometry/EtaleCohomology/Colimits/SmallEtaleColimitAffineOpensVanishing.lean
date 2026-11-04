module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocyclePresentation

/-!
# The first geometric hypothesis of Stacks 09YQ, from a presentation on Mathlib's small étale sites

In the namespace `Stacks.EtaleCohomology`, the theorem
`QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation` is the
hypothesis `haff` of
`SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` for a system
presented **on the raised small affine étale sites** of [Stacks, Tag 0EYL], in the restriction
vocabulary of `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem`.
The systems [Stacks, Tag 09YQ] speaks of live on Mathlib's small étale sites and carry their
presentation in the *inverse image* vocabulary. This file proves `haff` for a system presented in
that vocabulary.

## Main results

* `Stacks.EtaleCohomology.QcqsLimitCohomology.injective_levelCocycleSystem_obj` — the sheaf of
  `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` at a level is injective as
  soon as the system is pointwise injective.
* `Stacks.EtaleCohomology.QcqsLimitCohomology.injective_split_levelCocycleSystem_obj` — so is the
  sheaf of the split system, the splitting exhibiting it as a retract.
* `QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation` (in
  `Stacks.EtaleCohomology`) — **`haff` for an abelian sheaf on Mathlib's small étale site of the
  limit presented as `colim_i f_i^{-1}F_i` there, with every `F_i` injective.**

## Implementation notes

`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` is the system read on the levels
of [Stacks, Tag 0EYL] — transition data satisfying the cocycle law and no identity law — and
`Stacks.EtaleCohomology.AffineLimitCohomology.isColimitPresentation_levelCocycleSystem` presents
it there out of the two halves
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_iff` splits the
presentation predicate of [Stacks, Tag 09YQ] into. In `CategoryTheory.Sites.InverseSystem`,
`InverseSystemOfFiniteSites.AbelianCocycleSystem.isColimitPresentation_split` turns that into a
presentation of a genuine `AbelianSheafSystem`, by splitting the identity arrows' idempotents,
and that is the shape of the hypothesis of `haff`.

**Injectivity survives both steps, and neither step is a hypothesis.** Restriction of abelian
sheaves from Mathlib's small étale site of `X_n` to the level `n` is an equivalence
(`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`), and an
equivalence preserves injective objects — `CategoryTheory.Functor.PreservesInjectiveObjects` holds
for it by instance search alone. The sheaf of the split system at a level is a *retract* of the
sheaf of the cocycle data there, the two composites of the splitting being the identity and the
idempotent, and a retract of an injective object is injective
(`CategoryTheory.Retract.injective`). So pointwise injectivity of the system on Mathlib's sites is
pointwise injectivity of the split system on the levels, with nothing added.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex)

universe v u

namespace Stacks.EtaleCohomology.QcqsLimitCohomology

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]
  (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})

/-- **A level of [Stacks, Tag 0EYL] reads an injective abelian étale sheaf as an injective
object.** If every sheaf of the system is injective on Mathlib's small étale site of its stage,
then the sheaf of `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` at each level
is injective there.

Restriction along the level crossing is an equivalence by
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`, and an
equivalence preserves injective objects. Nothing is assumed beyond the pointwise injectivity. -/
theorem injective_levelCocycleSystem_obj (hF : ∀ i : Iᵒᵖ, Injective (F.obj i))
    (n : (sys D c B hD hX hc).I) :
    Injective ((levelCocycleSystem D c B hD hX hc F).obj n) := by
  let := isEquivalence_levelEtaleRestrictionAb D c B hD hX hc n
  have := hF (levelIndex D c B hD hX hc n)
  exact Functor.injective_obj (levelEtaleRestrictAb D c B hD hX hc n)
    (F.obj (levelIndex D c B hD hX hc n))

/-- **The split system of a pointwise injective system is pointwise injective.** The sheaf of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem.split` at a
level is a retract of the sheaf of the cocycle data there — the inclusion followed by the
projection of the splitting is the identity — so
`CategoryTheory.Retract.injective` applies to
`Stacks.EtaleCohomology.QcqsLimitCohomology.injective_levelCocycleSystem_obj`. -/
theorem injective_split_levelCocycleSystem_obj (hF : ∀ i : Iᵒᵖ, Injective (F.obj i))
    (S : ∀ n, (levelCocycleSystem D c B hD hX hc F).Splitting n)
    (n : (sys D c B hD hX hc).I) :
    Injective (((levelCocycleSystem D c B hD hX hc F).split S).obj n) := by
  have := injective_levelCocycleSystem_obj D c B hD hX hc F hF n
  exact Retract.injective ⟨(S n).incl, (S n).proj, (S n).incl_proj⟩

variable (𝓕 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt)
  AddCommGrpCat.{max u v + 1})

include B hD hX hc in
/-- **The first geometric hypothesis of [Stacks, Tag 09YQ], for a system presented on Mathlib's
small étale sites.** Let `(X_i)` be an inverse system of schemes over a nonempty directed index
with affine transition morphisms, all objects of a big étale site `B`, let `X` be the vertex of a
limit cone, let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i` in
the sense of [Stacks, Tag 0EZL] with every `F_i` **injective**, and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be
a compatible family exhibiting `𝓕 = colim_i f_i^{-1}F_i`. Then for every affine open `V` of `X`
the restriction of `𝓕` to the small étale site of `V` has vanishing global cohomology in every
positive degree.

This is `subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation` with its hypothesis
supplied by `isColimitPresentation_levelCocycleSystem`,
`InverseSystemOfFiniteSites.AbelianCocycleSystem.isColimitPresentation_split` and
`injective_split_levelCocycleSystem_obj`. -/
theorem subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation
    (hF : ∀ i : Iᵒᵖ, Injective (F.obj i))
    (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    (V : (c.pt).Opens) (hV : AlgebraicGeometry.IsAffineOpen V) (p : ℕ) (hp : 0 < p) :
    Subsingleton (Sheaf.H.{max u v + 1}
      ((OpensAcyclicity.smallEtaleOpensRestrict (c.pt) V).obj 𝓕) p) :=
  subsingleton_H_smallEtaleOpensRestrict_of_affineSitePresentation D c B hD hX hc 𝓕
    ((levelCocycleSystem D c B hD hX hc F).split
      (levelCocycleSystem D c B hD hX hc F).splitting) _
    ((levelCocycleSystem D c B hD hX hc F).isColimitPresentation_split
      (levelCocycleSystem D c B hD hX hc F).splitting
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (AffineEtaleModel.precoverage B (c.pt) hX) _ _
      (isColimitPresentation_levelCocycleSystem D c B hD hX hc F 𝓕 ι hpres hι))
    (injective_split_levelCocycleSystem_obj D c B hD hX hc F hF _) V hV p hp

end Stacks.EtaleCohomology.QcqsLimitCohomology

end
