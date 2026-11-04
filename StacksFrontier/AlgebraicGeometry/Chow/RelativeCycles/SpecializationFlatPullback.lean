module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Specialization of cycles commutes with flat pullback

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let `X` be a
scheme locally of finite type over `R`, and let `p : X' ⟶ X` be locally of finite type, flat and
of relative dimension `e`. On each fibre `p` induces a morphism `X'_s ⟶ X_s` which is again flat,
locally of finite type and of relative dimension `e`, so flat pullback along it is a
homomorphism `Z_r(X_s) ⟶ Z_{r+e}(X'_s)`. This file proves that for `r ≥ 0` the square
```
  Z_{r+e}(X'_K) -- sp_{X'/R} --> Z_{r+e}(X'_κ)
       ↑                              ↑
  Z_r(X_K)      -- sp_{X/R}  --> Z_r(X_κ)
```
commutes, the vertical arrows being flat pullback.

## Main results

* `Stacks.Chow.specializationCycle_fiberCycleFlatPullback_integralGenericCycle` — the case of a
  single integral closed subscheme of the generic fibre, which is the whole of the source's
  proof.
* `Stacks.Chow.fiberCycleFlatPullback_comp_specializationCycleHom` — **Stacks Project,
  Tag 0H4L**: the square commutes.
* `Stacks.Chow.specializationCycle_fiberCycleFlatPullback` — the same identity read on a cycle
  rather than as an equality of homomorphisms.
* `Stacks.Chow.specializationCycle_baseChangedFiberCycleFlatPullback` — the identity for the
  base change of `p` to the spectrum of a discrete valuation ring over the base, the shape in
  which the valuative criterion of Definition 0H50 consumes it.

## Implementation notes

The proof is the source's. For an integral closed subscheme `Z ⊆ X_K` of dimension `r` with
generic point `ξ`, let `\overline{Z} ⊆ X` be its scheme-theoretic image, which is the integral
closed subscheme of `X` with the same generic point. Its generic fibre is `Z` again, so the
member of the family `[\overline{Z}/X/Spec R]_r` over the generic point is `[Z]`; it dominates
`Spec R`, hence is flat over the discrete valuation ring
(`Stacks.Chow.flat_subschemeι_specializationClosure_comp`), so by Tag 0H4J its member over the
closed point is `sp_{X/R}([Z])`. The inverse image `Z' = \overline{Z} ×_X X'` is flat over `R`
too, its projection to `\overline{Z}` being a base change of `p`, and the flat pullback of
`[\overline{Z}/X/Spec R]_r` is `[Z'/X'/Spec R]_{r+e}` by the flat-pullback clause of Tag 0H4T,
which is Chow Homology, Lemma 02RE on each fibre. Tag 0H4J applied to `Z'` over `R` therefore
identifies both routes around the square with the member of `[Z'/X'/Spec R]_{r+e}` over the
closed point.

The passage from a single integral closed subscheme to an arbitrary cycle is not formal: a cycle
on `X_K` is only locally finite, both specialization maps are coefficientwise locally finite sums
over the points of a generic fibre, and the two index sets are related by the map of fibres
`X'_K ⟶ X_K`, so the sum over `X'_K` has to be regrouped along its fibres and each group summed
separately. That regrouping only uses that flat pullback multiplies coefficients by a weight read
through a map of fibres, which is `Stacks.Chow.exists_coeff_fiberCycleFlatPullback`; it is the
same argument as for the base change maps of Section 0H4E in
`Stacks.Chow.baseChangeFiberCycleOfEq_comp_specializationCycleHom_of_generator`.

## References

* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Lemma 0H4J](https://stacks.math.columbia.edu/tag/0H4J)
* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The inverse image of a closed subscheme along a flat morphism of the source -/

/-- The scheme-theoretic inverse image in `U` of a closed subscheme `i : Z ⟶ X` flat over the
base is again flat over the base: that inverse image projects to `Z` by the base change of `j`
along `i`, which is flat, and `Z` is flat over the base. -/
theorem flat_pullbackSnd_comp_of_flat {X S U Z : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [Flat j] (h : j ≫ f = fU) (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : Flat (i ≫ f)) : Flat (pullback.snd i j ≫ fU) := by
  have heq : pullback.snd i j ≫ fU = pullback.fst i j ≫ (i ≫ f) := by
    rw [← h, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hfst : Flat (pullback.fst i j) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback i j).flip inferInstance
  rw [heq]
  exact @Flat.comp _ _ _ _ _ hfst hi

/-! ### Coefficients of a flat pullback of fibrewise cycles -/

/-- Flat pullback of fibrewise cycles multiplies coefficients by a weight read through the
induced morphism of fibres: there are a map `q : U_s → X_s` on points and a weight function `m`
on `U_s`, both independent of the cycle, with `(j^*z)(y) = z(q y) * m y`.

The map `q` is the morphism of scheme-theoretic fibres induced by `j` and `m y` is the
multiplicity with which `y` enters the inverse image of the reduced closure of `q y`; this
existence statement is the form in which the two are used below. -/
theorem exists_coeff_fiberCycleFlatPullback {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) (s : S) (r : ℕ) :
    ∃ q : fU.fiber s → f.fiber s, ∃ m : fU.fiber s → ℤ,
      ∀ (z : FiberCycleGroup f s r) (y : fU.fiber s),
        (fiberCycleFlatPullback f fU j h e he s r z).1 y = z.1 (q y) * m y :=
  ⟨fun y ↦ fiberRestrict f fU j h s y,
    fun y ↦ flatPullbackWeight (fieldChowSituation (S.residueField s))
      (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s) ((r : ℤ) + (e : ℤ)) y,
    fun z y ↦ fiberCycleFlatPullback_apply f fU j h e he s r z y⟩

/-! ### Tag 0H4L -/

section FlatPullback

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X X' : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (fX' : X' ⟶ Spec (.of R))
  [LocallyOfFiniteType fX'] (p : X' ⟶ X) [LocallyOfFiniteType p] [Flat p] (hp : p ≫ f = fX')
  (e : ℕ) (he : AlgebraicGeometry.RelativeDimension p e) (r : ℕ)

/-- **The integral-subscheme case of Stacks Project, Lemma 0H4L**, which is the whole of the
source's proof. For an integral closed subscheme `Z ⊆ X_K` of dimension `r` with generic point
`ξ`, the specialization of the flat pullback of `[Z]` to `X'_K` is the flat pullback to `X'_κ` of
`sp_{X/R}([Z])`.

Let `\overline{Z} ⊆ X` be the scheme-theoretic image of `Z` in `X`, the integral closed subscheme
of `X` with generic point the image of `ξ`. Its generic fibre is `Z` again, so the member of the
family `[\overline{Z}/X/Spec R]_r` over the generic point is `[Z]`; it dominates `Spec R`, hence
is flat over it, so by Tag 0H4J its member over the closed point is `sp_{X/R}([Z])`. The flat
pullback of that family along `p` is the family `[\overline{Z} ×_X X'/X'/Spec R]_{r+e}` of the
scheme-theoretic inverse image, by the flat-pullback clause of Tag 0H4T; that inverse image is
flat over `R` as well, so Tag 0H4J over `R` identifies the member of the pulled-back family over
the generic point with its member over the closed point. Both routes around the square are those
two members. -/
theorem specializationCycle_fiberCycleFlatPullback_integralGenericCycle
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hd : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    specializationCycle fX' (r + e)
        (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r
          (integralGenericCycle f r ξ)) =
      fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
        (specializationCycle f r (integralGenericCycle f r ξ)) := by
  have : Flat ((specializationClosure f ξ).subschemeι ≫ f) :=
    flat_subschemeι_specializationClosure_comp f ξ
  have hZ := topologicalKrullDim_pullback_specializationClosure_le f r ξ hd
  have hgen := familyAssociatedToClosedSubscheme_specializationClosure_genericPoint f r ξ
  have hclosed : familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r
      (IsLocalRing.closedPoint R) = specializationCycle f r (integralGenericCycle f r ξ) := by
    rw [← hgen]
    exact (specializationCycle_familyAssociatedToClosedSubscheme_genericPoint f
      (specializationClosure f ξ).subschemeι r hZ).symm
  have : Flat (pullback.snd (specializationClosure f ξ).subschemeι p ≫ fX') :=
    flat_pullbackSnd_comp_of_flat f fX' p hp (specializationClosure f ξ).subschemeι inferInstance
  have h4t := familyAssociatedToClosedSubscheme_flatPullback f fX' p hp e he
    (specializationClosure f ξ).subschemeι r hZ
  have h4j := specializationCycle_familyAssociatedToClosedSubscheme_genericPoint fX'
    (pullback.snd (specializationClosure f ξ).subschemeι p) (r + e)
    (fibreDim_flatPullbackClosedSubscheme_le f fX' p hp e he
      (specializationClosure f ξ).subschemeι r hZ)
  have key : specializationCycle fX' (r + e)
        (flatPullbackFamily f fX' p hp e he r
          (familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r)
          (genericPoint (Spec (.of R)))) =
      flatPullbackFamily f fX' p hp e he r
        (familyAssociatedToClosedSubscheme f (specializationClosure f ξ).subschemeι r)
        (IsLocalRing.closedPoint R) := by
    rw [h4t]
    exact h4j
  rw [← hclosed, ← hgen]
  exact key

/-- **Stacks Project, Lemma 0H4L.** Let `R` be a discrete valuation ring with fraction field `K`
and residue field `κ`, let `X` be a scheme locally of finite type over `R`, and let `p : X' ⟶ X`
be a morphism which is locally of finite type, flat and of relative dimension `e`. Then for
`r ≥ 0` the square formed by the specialization homomorphisms
`sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` and `sp_{X'/R} : Z_{r+e}(X'_K) ⟶ Z_{r+e}(X'_κ)` of
Section 0H4H and the flat pullbacks `Z_r(X_K) ⟶ Z_{r+e}(X'_K)`, `Z_r(X_κ) ⟶ Z_{r+e}(X'_κ)` of
Section 0H4N commutes.

The integral-subscheme case is
`Stacks.Chow.specializationCycle_fiberCycleFlatPullback_integralGenericCycle`. The passage from
it to an arbitrary cycle is the regrouping below: the coefficient of `sp_{X'/R}` of a flat
pullback is a locally finite sum over the points of `X'_K`, which is summed along the fibres of
`X'_K ⟶ X_K` and each fibre identified with the corresponding term of the flat pullback of
`sp_{X/R}`. -/
@[stacks 0H4L]
theorem fiberCycleFlatPullback_comp_specializationCycleHom :
    (fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r).comp
        (specializationCycleHom f r) =
      (specializationCycleHom fX' (r + e)).comp
        (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r) := by
  classical
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨q, m, hm⟩ := exists_coeff_fiberCycleFlatPullback f fX' p hp e he
    (genericPoint (Spec (.of R))) r
  obtain ⟨q₀, m₀, hm₀⟩ := exists_coeff_fiberCycleFlatPullback f fX' p hp e he
    (IsLocalRing.closedPoint R) r
  have hgroup : ∀ ξ : f.fiber (genericPoint (Spec (.of R))),
      (∑' z : q ⁻¹' {ξ},
          (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r c).1 z.1 *
            (specializationCycle fX' (r + e)
              (integralGenericCycle fX' (r + e) z.1)).1 x) =
        c.1 ξ * (fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
          (specializationCycle f r (integralGenericCycle f r ξ))).1 x := by
    intro ξ
    by_cases hd : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)
    · have hsupp : Function.support (fun z ↦
          (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r
              (integralGenericCycle f r ξ)).1 z *
            (specializationCycle fX' (r + e)
              (integralGenericCycle fX' (r + e) z)).1 x) ⊆ q ⁻¹' {ξ} := by
        intro z hz
        by_contra hne
        have h0 : (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r
            (integralGenericCycle f r ξ)).1 z = 0 := by
          rw [hm (integralGenericCycle f r ξ) z,
            integralGenericCycle_apply_eq_zero f r ξ (q z) (Or.inl hne), zero_mul]
        exact hz (by simp only [h0, zero_mul])
      have hA := (hasSum_subtype_iff_of_support_subset hsupp).2
        (hasSum_specializationCycle_of_forall fX' (r + e)
          (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r
            (integralGenericCycle f r ξ)) x)
      have hB : HasSum (fun z : q ⁻¹' {ξ} ↦
          (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r c).1 z.1 *
            (specializationCycle fX' (r + e)
              (integralGenericCycle fX' (r + e) z.1)).1 x)
          (c.1 ξ * (specializationCycle fX' (r + e)
            (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r
              (integralGenericCycle f r ξ))).1 x) := by
        refine (hA.mul_left (c.1 ξ)).congr_fun ?_
        intro z
        have hz : q z.1 = ξ := z.2
        simp only [Function.comp_apply]
        rw [hm c z.1, hm (integralGenericCycle f r ξ) z.1, hz,
          integralGenericCycle_apply_self f r ξ hd, one_mul, mul_assoc]
      rw [hB.tsum_eq, specializationCycle_fiberCycleFlatPullback_integralGenericCycle f fX' p hp
        e he r ξ hd]
    · have hc : c.1 ξ = 0 := by
        by_contra hne
        exact hd (fiberPointDimension_of_coeff_ne_zero f _ r c ξ hne)
      rw [hc, zero_mul, ← tsum_zero]
      refine tsum_congr fun z ↦ ?_
      have hz : q z.1 = ξ := z.2
      rw [hm c z.1, hz, hc, zero_mul, zero_mul]
  have hleft : HasSum (fun ξ : f.fiber (genericPoint (Spec (.of R))) ↦
      c.1 ξ * (fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
        (specializationCycle f r (integralGenericCycle f r ξ))).1 x)
      ((specializationCycle fX' (r + e)
        (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r c)).1 x) :=
    ((hasSum_specializationCycle_of_forall fX' (r + e)
      (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r c)
      x).tsum_fiberwise q).congr_fun fun ξ ↦ (hgroup ξ).symm
  have hright : HasSum (fun ξ : f.fiber (genericPoint (Spec (.of R))) ↦
      c.1 ξ * (fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
        (specializationCycle f r (integralGenericCycle f r ξ))).1 x)
      ((fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
        (specializationCycle f r c)).1 x) := by
    rw [hm₀ (specializationCycle f r c) x]
    refine ((hasSum_specializationCycle_of_forall f r c (q₀ x)).mul_right (m₀ x)).congr_fun ?_
    intro ξ
    rw [hm₀ (specializationCycle f r (integralGenericCycle f r ξ)) x, mul_assoc]
  exact hright.unique hleft

/-- **Stacks Project, Lemma 0H4L**, read on a cycle: the specialization of the flat pullback of
an `r`-cycle on the generic fibre is the flat pullback of its specialization. -/
theorem specializationCycle_fiberCycleFlatPullback
    (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    specializationCycle fX' (r + e)
        (fiberCycleFlatPullback f fX' p hp e he (genericPoint (Spec (.of R))) r c) =
      fiberCycleFlatPullback f fX' p hp e he (IsLocalRing.closedPoint R) r
        (specializationCycle f r c) :=
  (DFunLike.congr_fun
    (fiberCycleFlatPullback_comp_specializationCycleHom f fX' p hp e he r) c).symm

end FlatPullback

/-- **Stacks Project, Lemma 0H4L** for the base change of a flat morphism of the source to the
spectrum of a discrete valuation ring over the base. This is the shape in which the valuative
condition of Definition 0H50 compares the two members of a flat pullback of a family of cycles on
fibres: `Stacks.Chow.baseChangedFiberCycleFlatPullback` is flat pullback along the base change of
`j`, which is again flat, locally of finite type and of relative dimension `e`. -/
@[stacks 0H4L "for the base change of the flat morphism to the spectrum of a discrete \
valuation ring over the base"]
theorem specializationCycle_baseChangedFiberCycleFlatPullback {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [LocallyOfFiniteType j] [Flat j] (h : j ≫ f = fU) (e : ℕ)
    (he : AlgebraicGeometry.RelativeDimension j e) {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (g : Spec (.of R) ⟶ S) (r : ℕ)
    (c : FiberCycleGroup (pullback.snd f g) (genericPoint (Spec (.of R))) r) :
    baseChangedFiberCycleFlatPullback f fU j h e he g (IsLocalRing.closedPoint R) r
        (specializationCycle (pullback.snd f g) r c) =
      specializationCycle (pullback.snd fU g) (r + e)
        (baseChangedFiberCycleFlatPullback f fU j h e he g
          (genericPoint (Spec (.of R))) r c) :=
  (specializationCycle_fiberCycleFlatPullback (pullback.snd f g) (pullback.snd fU g)
    (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) e
    (relativeDimension_pullbackRestrict f fU j h g he) r c).symm

end Stacks.Chow

end
