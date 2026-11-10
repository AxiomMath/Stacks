module

public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint

/-!
# Smoothness at a point, standard smoothness, and the Jacobian criterion

Of the six conditions of Stacks Tag 01V9, three make no reference to flatness, to the
scheme-theoretic fibre, or to the sheaf of relative differentials: smoothness at the point,
condition (1); the existence of a standard smooth affine neighbourhood, condition (5); and the
existence of an affine presentation whose chosen Jacobian minor does not vanish at the point,
condition (6).  **This file proves that those three are equivalent.**

The equivalence is proved without the hypothesis that `f` is locally of finite presentation,
which the source assumes throughout, so it is slightly stronger than the corresponding part of
the source's statement.  It is also a complete equivalence, not a cycle through the remaining
three conditions: nothing below mentions conditions (2), (3) or (4).

## Main results

* `Stacks.SmoothAtJacobian.condition1_iff_condition5`: smoothness at a point is equivalent to
  standard smoothness on affine neighbourhoods.
* `Stacks.SmoothAtJacobian.condition5_imp_condition6`: a standard smooth affine neighbourhood
  yields a presentation whose Jacobian is a unit, hence does not vanish at the point.
* `Stacks.SmoothAtJacobian.condition6_imp_condition1`: a presentation whose Jacobian does not
  vanish at the point yields smoothness at that point.
* `Stacks.SmoothAtJacobian.tfae_condition1_condition5_condition6`: the three are equivalent.

## Implementation notes

Condition (1) and condition (5) differ only in that the former leaves the affine neighbourhood
of the image point unspecified while the latter asserts its existence.  The content of their
equivalence is `InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth` (Tag 01V7),
which is the same statement with that neighbourhood *prescribed*; the affine opens of a scheme
form a basis of its topology, so the image point has one, and that is the whole proof.

Condition (5) implies condition (6) because standard smoothness is the existence of a
*submersive* presentation, whose Jacobian is by definition a unit, and a unit lies in no prime
ideal.  The index types of a submersive presentation are merely finite, so they are transported
along `Fintype.equivFin` to the `Fin n` and `Fin c` that condition (6) asks for; the Jacobian is
invariant under that reindexing.  Passing between the morphism restricted to the two affine
opens and the map it induces on sections is done with
`AlgebraicGeometry.arrowResLEAppIso`, along which standard smoothness of a ring map transports.

Condition (6) implies condition (1) by shrinking the affine neighbourhood of `x` to the locus
where the Jacobian is invertible.  On the basic open of the Jacobian the sections are the
localization away from it, and the canonical pre-submersive presentation of a localization away
from an element composes with the given presentation to a presentation whose Jacobian is the
square of the image of the Jacobian, hence a unit.  So the composite presentation is submersive,
the restriction to that basic open is standard smooth, and Tag 01V7 applies in the other
direction.  The point lies in that basic open precisely because the Jacobian does not vanish
there, which is the hypothesis of condition (6) read through
`AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 01V7](https://stacks.math.columbia.edu/tag/01V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.SmoothAtJacobian

attribute [local instance] Fintype.ofFinite

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- **Condition (1) of Tag 01V9 is equivalent to condition (5).** A morphism is smooth at a
point exactly when some affine open neighbourhood of the point, lying over some affine open of
the base, carries a standard smooth restriction of the morphism. -/
public theorem condition1_iff_condition5 : Condition1 f x ↔ Condition5 f x := by
  constructor
  · intro hf
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨U, hU, hxU, hUV, hs⟩ :=
      (InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth f x V hV hxV).1 hf
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hUV, hs⟩
  · rintro ⟨U, V, hxU, hUV, hs⟩
    exact (InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth f x V.1 V.2
      (hUV hxU)).2 ⟨U.1, U.2, hxU, hUV, hs⟩

/-- Standardly smooth restriction of a morphism is the same as standard smoothness of the induced
map on sections. -/
private theorem isStandardSmooth_resLE_iff {V : S.affineOpens} {U : X.affineOpens}
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    IsStandardSmooth (f.resLE V.1 U.1 hUV) ↔ (f.appLE V.1 U.1 hUV).hom.IsStandardSmooth :=
  RingHom.isStandardSmooth_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V.1 U.1 hUV)

/-- **Condition (5) of Tag 01V9 implies condition (6).** A standard smooth restriction is given
by a submersive presentation, whose Jacobian is a unit and therefore lies in no prime ideal, in
particular not in the prime of the point. -/
public theorem condition5_imp_condition6 : Condition5 f x → Condition6 f x := by
  rintro ⟨U, V, hxU, hUV, hs⟩
  have hstd := (isStandardSmooth_resLE_iff f hUV).mp hs
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hstd.out
  set Q := P.reindex (Fintype.equivFin ι).symm (Fintype.equivFin σ).symm
  refine ⟨U, V, hxU, hUV, Fintype.card ι, Fintype.card σ,
    Q.toPreSubmersivePresentation, fun hmem => ?_⟩
  exact (U.2.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hmem Q.jacobian_isUnit)

/-- **Condition (6) of Tag 01V9 implies condition (1).** On the basic open of the Jacobian the
given presentation becomes submersive, so the morphism is standard smooth there; and the point
lies in that basic open because the Jacobian does not vanish at it. -/
public theorem condition6_imp_condition1 : Condition6 f x → Condition1 f x := by
  rintro ⟨U, V, hxU, hUV, n, c, P, hr⟩
  let : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  set r := P.jacobian
  set W : X.Opens := X.basicOpen r
  have hxW : x ∈ W := by
    change x ∈ X.basicOpen r
    have hp : U.2.isoSpec.hom ⟨x, hxU⟩ ∈ PrimeSpectrum.basicOpen r := hr
    rw [← U.2.fromSpec_preimage_basicOpen] at hp
    change U.2.fromSpec (U.2.isoSpec.hom ⟨x, hxU⟩) ∈ X.basicOpen r at hp
    have heq : U.2.fromSpec (U.2.isoSpec.hom ⟨x, hxU⟩) = x := by
      change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨x, hxU⟩ = x
      rw [U.2.isoSpec_hom_fromSpec]
      rfl
    rwa [heq] at hp
  have hWV : W ≤ f ⁻¹ᵁ V.1 := (X.basicOpen_le r).trans hUV
  let : IsLocalization.Away r Γ(X, W) := U.2.isLocalization_basicOpen r
  let : Algebra Γ(X, U.1) Γ(X, W) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  have happ : f.appLE V.1 W hWV =
      f.appLE V.1 U.1 hUV ≫ X.presheaf.map (homOfLE (X.basicOpen_le r)).op := by
    rw [← f.appLE_map hUV (homOfLE (X.basicOpen_le r)).op]
  let : Algebra Γ(S, V.1) Γ(X, W) := (f.appLE V.1 W hWV).hom.toAlgebra
  let : IsScalarTower Γ(S, V.1) Γ(X, U.1) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom happ)
  set Q := Algebra.PreSubmersivePresentation.localizationAway
    (R := Γ(X, U.1)) (Γ(X, W)) r
  have hru : IsUnit (algebraMap Γ(X, U.1) Γ(X, W) r) :=
    IsLocalization.map_units (M := Submonoid.powers r) Γ(X, W) ⟨r, Submonoid.mem_powers r⟩
  have hunit : IsUnit (Q.comp P).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian Q P,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact hru.mul hru
  let QP : Algebra.SubmersivePresentation Γ(S, V.1) Γ(X, W) (Unit ⊕ Fin n) (Unit ⊕ Fin c) :=
    ⟨Q.comp P, hunit⟩
  have hstdW : (f.appLE V.1 W hWV).hom.IsStandardSmooth := QP.isStandardSmooth
  exact (condition1_iff_condition5 f x).2
    ⟨⟨W, U.2.basicOpen r⟩, V, hxW, hWV, (isStandardSmooth_resLE_iff f hWV).mpr hstdW⟩

/-- **Three of the six conditions of Tag 01V9 are equivalent**, with no finiteness hypothesis on
the morphism: smoothness at the point, condition (1); a standard smooth affine neighbourhood,
condition (5); and an affine presentation whose chosen Jacobian minor does not vanish at the
point, condition (6). -/
public theorem tfae_condition1_condition5_condition6 :
    [Condition1 f x, Condition5 f x, Condition6 f x].TFAE := by
  tfae_have 1 ↔ 2 := condition1_iff_condition5 f x
  tfae_have 2 → 3 := condition5_imp_condition6 f x
  tfae_have 3 → 1 := condition6_imp_condition1 f x
  tfae_finish

end Stacks.SmoothAtJacobian

end
