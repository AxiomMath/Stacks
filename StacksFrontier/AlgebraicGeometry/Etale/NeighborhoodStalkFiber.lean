module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# The unique point over `x` in a base change to the local ring of an étale neighbourhood

Let `f : X ⟶ S` be a morphism of schemes, `x` a point of `X` and `U` an *elementary* étale
neighbourhood of `(S, f x)`. Write `b : Spec 𝒪_{U, u} ⟶ S` for the composite of
`Scheme.fromSpecStalk` at the distinguished point `u` of `U` with the structure morphism of `U`.
Then `X ×_S Spec 𝒪_{U, u}` has exactly one point lying over `x`.

This is the uniqueness assertion built into the statements of the Stacks Project's "after an
elementary étale neighbourhood" propositions — Tags 05I5, 05ID, 05KY, 05KZ and 05MF all speak of
*the unique point* of `X ×_S Spec 𝒪_{S', s'}` mapping to `x`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.eq_of_specializes`: a locally quasi-finite morphism identifies
  any two points of its source which are related by a specialization and have the same image.
* `AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks`: a morphism which is
  surjective on stalks induces isomorphisms on residue fields.
* `AlgebraicGeometry.Scheme.eq_of_fromSpecStalk_eq`: for an étale `g : U ⟶ S`, a point of
  `Spec 𝒪_{U, p}` whose image in `S` is `g p` is the point lying over `p`.
* `AlgebraicGeometry.EtaleNeighborhood.exists_preimage_fst_eq_singleton` and
  `AlgebraicGeometry.EtaleNeighborhood.preimage_fst_eq_singleton_of_apply_eq`: the fibre of
  `pullback.fst f b` over `x` is a singleton, in existence and in uniqueness form.

## Implementation notes

The distinguished point of `Spec 𝒪_{U, u}` is handled through the hypothesis
`U.scheme.fromSpecStalk U.point y = U.point` on a *variable* `y` rather than by writing
`IsLocalRing.closedPoint` into the statements. The term `IsLocalRing.closedPoint R` for
`R : CommRingCat` inhabits `↥(Spec R)` only up to unfolding `Spec`, so goals mentioning it are
not type-correct at `implicit` transparency and `rw` refuses to build a motive for them;
quantifying over `y` keeps every intermediate goal well-typed with no transparency option.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

-- Makes `Unramified`, and the properties it implies, available from `Etale` by instance search.
attribute [instance] unramified_of_etale

/-- Two points of the source of a locally quasi-finite morphism which are related by a
specialization and lie over the same point of the target are equal. -/
theorem Scheme.Hom.eq_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x₁ x₂ : X} (h : x₁ ⤳ x₂) (he : f x₁ = f x₂) : x₁ = x₂ :=
  (f.isDiscrete_preimage_singleton (f x₂)).eq_of_specializes h he rfl

/-- A morphism which is surjective on stalks induces an isomorphism on residue fields at every
point. -/
theorem Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : IsIso (f.residueFieldMap x) := by
  have hsurj : Function.Surjective (f.residueFieldMap x).hom := by
    have h : Function.Surjective ((f.residueFieldMap x).hom ∘ (Y.residue (f x)).hom) := by
      rw [← RingHom.coe_comp, ← CommRingCat.hom_comp, Scheme.residue_residueFieldMap,
        CommRingCat.hom_comp, RingHom.coe_comp]
      exact (X.residue_surjective x).comp (f.stalkMap_surjective x)
    exact Function.Surjective.of_comp h
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(f.residueFieldMap x).hom.injective, hsurj⟩

/-- For an étale morphism `g : U ⟶ S` and a point `p` of `U`, a point of `Spec 𝒪_{U, p}` whose
image in `S` is `g p` is the point lying over `p`. -/
theorem Scheme.eq_of_fromSpecStalk_eq {U S : Scheme.{u}} (g : U ⟶ S) [Etale g] (p : U)
    {y z : ↥(Spec (U.presheaf.stalk p))} (hz : U.fromSpecStalk p z = p)
    (h : g (U.fromSpecStalk p y) = g p) : y = z := by
  have hspec : U.fromSpecStalk p y ⤳ p := by
    simpa [Scheme.range_fromSpecStalk] using Set.mem_range_self (f := U.fromSpecStalk p) y
  exact (U.fromSpecStalk p).isEmbedding.injective
    ((g.eq_of_specializes hspec h).trans hz.symm)

namespace EtaleNeighborhood

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- `Spec 𝒪_{U, u}` has a point lying over the distinguished point `u` of an étale
neighbourhood `U`, namely the closed point. -/
theorem exists_fromSpecStalk_eq_point (U : EtaleNeighborhood S (f x)) :
    ∃ y : ↥(Spec (U.scheme.presheaf.stalk U.point)),
      U.scheme.fromSpecStalk U.point y = U.point :=
  ⟨closedPoint (U.scheme.presheaf.stalk U.point), Scheme.fromSpecStalk_closedPoint⟩

variable {U : EtaleNeighborhood S (f x)} {y : ↥(Spec (U.scheme.presheaf.stalk U.point))}
  (hy : U.scheme.fromSpecStalk U.point y = U.point)

include hy

/-- The point of `Spec 𝒪_{U, u}` lying over the distinguished point of `U` maps to `f x`. -/
private theorem fromSpecStalk_toBase_apply :
    (U.scheme.fromSpecStalk U.point ≫ U.toBase) y = f x := by
  rw [Scheme.Hom.comp_apply, hy, U.map_point]

/-- Conversely, the point of `Spec 𝒪_{U, u}` lying over the distinguished point of `U` is the
only one mapping to `f x`. -/
private theorem eq_of_fromSpecStalk_toBase_eq
    {z : ↥(Spec (U.scheme.presheaf.stalk U.point))}
    (h : (U.scheme.fromSpecStalk U.point ≫ U.toBase) z = f x) : z = y :=
  Scheme.eq_of_fromSpecStalk_eq U.toBase U.point hy (by rwa [U.map_point])

/-- For an elementary neighbourhood, `Spec 𝒪_{U, u} ⟶ S` induces an isomorphism of residue
fields at the point lying over the distinguished point of `U`. -/
private theorem isIso_fromSpecStalk_toBase_residueFieldMap (hU : U.IsElementary) :
    IsIso ((U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap y) := by
  have h1 : IsIso (U.toBase.residueFieldMap (U.scheme.fromSpecStalk U.point y)) :=
    (U.toBase.isIso_residueFieldMap_congr hy).mpr ((isElementary_iff U).mp hU)
  have h2 := (U.scheme.fromSpecStalk U.point).isIso_residueFieldMap_of_surjectiveOnStalks y
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' h1 h2

open Scheme.Pullback in
/-- **The unique point over `x`.** If `U` is an elementary étale neighbourhood of `(S, f x)`,
then `X ×_S Spec 𝒪_{U, u}` has exactly one point lying over `x`. -/
private theorem preimage_fst_eq_singleton_aux (hU : U.IsElementary) :
    ∃ v : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} = {v} := by
  let T : Triplet f (U.scheme.fromSpecStalk U.point ≫ U.toBase) :=
    ⟨x, y, f x, rfl, fromSpecStalk_toBase_apply f x hy⟩
  have hiso : IsIso ((S.residueFieldCongr T.hy).inv ≫
      (U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap T.y) := by
    have := isIso_fromSpecStalk_toBase_residueFieldMap f x hy hU
    infer_instance
  have htl : IsIso T.tensorInl :=
    (IsPushout.of_hasPushout ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫
        (U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap T.y)).isIso_inl_of_isIso
  have hsub : Subsingleton ↑(Spec T.tensor) :=
    (PrimeSpectrum.comap_injective_of_surjective T.tensorInl.hom
      (ConcreteCategory.bijective_of_isIso T.tensorInl).2).subsingleton
  have hofPoint : ∀ t : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) t = x →
      Triplet.ofPoint t = T := by
    intro t ht
    refine Triplet.ext ht (eq_of_fromSpecStalk_toBase_eq f x hy ?_)
    have hcond : f (pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) t) =
        (U.scheme.fromSpecStalk U.point ≫ U.toBase)
          (pullback.snd f (U.scheme.fromSpecStalk U.point ≫ U.toBase) t) :=
      congr($(pullback.condition
        (f := f) (g := U.scheme.fromSpecStalk U.point ≫ U.toBase)) t)
    rw [Triplet.ofPoint_y, ← hcond, ht]
  obtain ⟨t, ht, -⟩ := T.exists_preimage
  refine ⟨t, Set.eq_singleton_iff_unique_mem.mpr ⟨ht, fun t' ht' => ?_⟩⟩
  have hsub2 : Subsingleton ↑(Spec (Triplet.ofPoint t).tensor) := by rwa [hofPoint t ht]
  have hsub3 : Subsingleton ↑(Spec (carrierEquiv t).fst.tensor) := hsub2
  exact carrierEquiv.injective (carrierEquiv_eq_iff.mpr
    ⟨(hofPoint t' ht').trans (hofPoint t ht).symm, Subsingleton.elim _ _⟩)

omit hy

variable (U)

/-- **The unique point over `x`, existence form.** For an elementary étale neighbourhood `U` of
`(S, f x)` the fibre of `X ×_S Spec 𝒪_{U, u} ⟶ X` over `x` is a singleton. -/
theorem exists_preimage_fst_eq_singleton (hU : U.IsElementary) :
    ∃ v : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
      pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} = {v} := by
  obtain ⟨y, hy⟩ := exists_fromSpecStalk_eq_point f x U
  exact preimage_fst_eq_singleton_aux f x hy hU

/-- **The unique point over `x`, uniqueness form.** For an elementary étale neighbourhood `U` of
`(S, f x)`, any point of `X ×_S Spec 𝒪_{U, u}` lying over `x` already exhausts the fibre
over `x`. -/
theorem preimage_fst_eq_singleton_of_apply_eq (hU : U.IsElementary)
    {v : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase))}
    (hv : pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) v = x) :
    pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} = {v} := by
  obtain ⟨w, hw⟩ := exists_preimage_fst_eq_singleton f x U hU
  have hmem : v ∈ pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) ⁻¹' {x} := hv
  rw [hw, Set.mem_singleton_iff] at hmem
  rw [hw, hmem]

end EtaleNeighborhood

end AlgebraicGeometry

end
