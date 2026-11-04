module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistStandardOpenMul

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L` is multiplicative

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra. Over a standard open of a positive-degree homogeneous element the
degreewise inclusion `Γ(D₊(f), 𝒪_P(i)) ⟶ Γ(D₊(f), π_* 𝒪_L)` is multiplicative, by
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_mul`. **This file extends that to every open
of `P`**, and reads the result on the homogeneous pieces of the graded algebra
`Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra`, where it is the statement that the
family `Stacks.AlgebraicGeometry.ProjConeTwist.coneIota` of inclusions multiplies as the grading
prescribes — the `ι_mul` condition of `AlgebraicGeometry.AbstractCone` for the cone of
[Stacks, Tag 062R], and the reason `π_* 𝒪_L` is the twist *algebra* and not merely the coproduct
of its homogeneous pieces.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.pushforwardStructureSheaf_map_mul`: restriction in the
  direct image of a structure sheaf is a ring homomorphism.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistHom_mul`: the glued degreewise inclusion is
  multiplicative over a standard open of a positive-degree homogeneous element.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistHom_mul_app`: **the glued degreewise inclusion
  is multiplicative over every open of `P`.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneIota_mul`: **the same on the homogeneous pieces of
  the algebra of nonnegative twists, in all integer degrees** — the `ι_mul` condition of a cone.

## Implementation notes

The extension from the standard opens to an arbitrary open is separatedness, in the form
`Stacks.BasisRestriction.moduleSheafSection_ext_onBasis`: the direct image is a sheaf of
`𝒪_P`-modules and the positive-degree standard opens are a basis, so two of its sections over an
open `U` agree as soon as they agree on every basis open inside `U`. There both sides restrict as
they should: the left-hand side by naturality of the inclusion and of the multiplication
(the `naturality` field of `SheafOfModules.BilinearMap`), the right-hand side because restriction
in the direct image is the restriction map of `𝒪_L`, hence a ring homomorphism — which is
`pushforwardStructureSheaf_map_mul`, the one statement that has to look through the definition of
the direct image.

Degrees are natural numbers until the last step, where the case distinction defining
`nonnegTwistingSheaf` and `nonnegTwistMul` is made: in a negative degree the piece is the zero
sheaf, so the section vanishes, the multiplication vanishes, and both sides of `coneIota_mul` are
zero. Products of sections of the direct image are formed in
`Stacks.AlgebraicGeometry.ProjConeTwist.coneSections`, the functions on the part of the cone
lying over the open, since the sections of a sheaf of modules carry no multiplication of their
own; this is the spelling `AlgebraicGeometry.AbstractCone` uses in its `ι_mul` field.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ring of functions on the part of the cone lying over an open of `P`. The sections of
`π_* 𝒪_L` over that open are the same thing, read as a module over the sections of `𝒪_P`. -/
abbrev coneSections (U : Opens (ProjectiveSpectrum.top 𝒜)) : Type u :=
  (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj (op (pi 𝒜 ⁻¹ᵁ U))

/-- **Restriction in the direct image of a structure sheaf is a ring homomorphism**: it is the
restriction map of `𝒪_L` along the inclusion of preimages. -/
theorem pushforwardStructureSheaf_map_mul {V U : Opens (ProjectiveSpectrum.top 𝒜)} (h : V ≤ U)
    (s t : coneSections 𝒜 U) :
    (show coneSections 𝒜 V from
        (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE h).op (s * t)) =
      (show coneSections 𝒜 V from
          (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE h).op s) *
        (show coneSections 𝒜 V from
          (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE h).op t) :=
  map_mul ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
    ((Opens.map (pi 𝒜).base).map (homOfLE h)).op).hom s t

/-- **The glued degreewise inclusion is multiplicative over a standard open** of a
positive-degree homogeneous element. -/
@[stacks 0EKG "the glued degreewise inclusion O_P(m) to pi_* O_L is multiplicative over a \
standard open of a positive-degree homogeneous element"]
theorem coneTwistHom_mul {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℕ)
    (x : (twistingSheaf 𝒜 (i : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 (j : ℤ)).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (show coneSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
        (coneTwistHom 𝒜 (i + j)).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f))
          (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)) =
      (show coneSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
          (coneTwistHom 𝒜 i).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x) *
        (show coneSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
          (coneTwistHom 𝒜 j).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f)) y) := by
  have hA := ConcreteCategory.congr_hom (coneTwistHom_app 𝒜 (i + j) hf hd)
    (natTwistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)
  have hB := ConcreteCategory.congr_hom (coneTwistHom_app 𝒜 i hf hd) x
  have hC := ConcreteCategory.congr_hom (coneTwistHom_app 𝒜 j hf hd) y
  have h := coneTwistApp_mul 𝒜 d hf hd i j x y
  exact hA.trans (h.trans (congrArg₂ (· * ·) hB.symm hC.symm))

/-- **The glued degreewise inclusion `𝒪_P(i) ⟶ π_* 𝒪_L` is multiplicative over every open of
`P`.** The standard opens of positive-degree homogeneous elements are a basis, and both sides
restrict to them as the standard-open statement says. -/
@[stacks 0EKG "the glued degreewise inclusion O_P(m) to pi_* O_L is multiplicative over every \
open of P, in nonnegative degrees"]
theorem coneTwistHom_mul_app (i j : ℕ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : (twistingSheaf 𝒜 (i : ℤ)).val.obj (op U))
    (b : (twistingSheaf 𝒜 (j : ℤ)).val.obj (op U)) :
    (show coneSections 𝒜 U from
        (coneTwistHom 𝒜 (i + j)).val.app (op U) (natTwistMulSection 𝒜 i j (op U) a b)) =
      (show coneSections 𝒜 U from (coneTwistHom 𝒜 i).val.app (op U) a) *
        (show coneSections 𝒜 U from (coneTwistHom 𝒜 j).val.app (op U) b) := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)) (positiveBasicOpen 𝒜)
    (isBasis_positiveBasicOpen 𝒜) _ _ fun p hle => ?_
  have hd : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hf : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have hL := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 (i + j)).val (homOfLE hle).op
    (natTwistMulSection 𝒜 i j (op U) a b)
  have hbil := (twistMul 𝒜 (i : ℤ) (j : ℤ)).naturality (homOfLE hle).op a b
  have hRa := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 i).val (homOfLE hle).op a
  have hRb := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 j).val (homOfLE hle).op b
  have hring := pushforwardStructureSheaf_map_mul 𝒜 hle
    ((coneTwistHom 𝒜 i).val.app (op U) a) ((coneTwistHom 𝒜 j).val.app (op U) b)
  have hloc := coneTwistHom_mul 𝒜 hf hd i j
    ((twistingSheaf 𝒜 (i : ℤ)).val.map (homOfLE hle).op a)
    ((twistingSheaf 𝒜 (j : ℤ)).val.map (homOfLE hle).op b)
  refine hL.symm.trans (Eq.trans ?_ hring.symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) hRa hRb)
  exact (congrArg _ hbil).trans hloc

/-- The inclusion `coneIota` sends the zero section of a piece to zero. -/
private theorem coneIota_app_eq_zero (n : ℤ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    {z : (nonnegTwistingSheaf 𝒜 n).val.obj (op U)} (hz : z = 0) :
    (show coneSections 𝒜 U from (coneIota 𝒜 n).val.app (op U) z) = 0 := by
  subst hz
  exact map_zero (ConcreteCategory.hom ((coneIota 𝒜 n).val.app (op U)))

/-- **The inclusions of the homogeneous pieces of the algebra of nonnegative twists in `π_* 𝒪_L`
multiply as the grading prescribes**, over every open of `P` and in all integer degrees. This is
the `ι_mul` condition of `AlgebraicGeometry.AbstractCone` for the cone of the truncation algebra,
graded by `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra`. In a negative degree the
piece is the zero sheaf, so both sides vanish. -/
@[stacks 0EKG "the inclusions of the homogeneous pieces of the nonnegative twist algebra in \
pi_* O_L are multiplicative, over every open of P and in every integer degree, for the \
truncation cone"]
theorem coneIota_mul (i j : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : (nonnegTwistingSheaf 𝒜 i).val.obj (op U))
    (b : (nonnegTwistingSheaf 𝒜 j).val.obj (op U)) :
    (show coneSections 𝒜 U from
        (coneIota 𝒜 (i + j)).val.app (op U) ((nonnegTwistMul 𝒜 i j).app (op U) a b)) =
      (show coneSections 𝒜 U from (coneIota 𝒜 i).val.app (op U) a) *
        (show coneSections 𝒜 U from (coneIota 𝒜 j).val.app (op U) b) := by
  rcases lt_or_ge i 0 with hi | hi
  · exact (coneIota_app_eq_zero 𝒜 _ (nonnegTwistMul_eq_zero_of_neg_left 𝒜 hi (op U) a b)).trans
      ((zero_mul _).symm.trans (congrArg (· * _) (coneIota_app_eq_zero 𝒜 i
        (eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 hi) a)).symm))
  rcases lt_or_ge j 0 with hj | hj
  · exact (coneIota_app_eq_zero 𝒜 _ (nonnegTwistMul_eq_zero_of_neg_right 𝒜 hj (op U) a b)).trans
      ((mul_zero _).symm.trans (congrArg (_ * ·) (coneIota_app_eq_zero 𝒜 j
        (eq_zero_of_isZero (isZero_nonnegTwistingSheaf 𝒜 hj) b)).symm))
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = (m : ℤ) := ⟨i.toNat, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, by omega⟩
  exact coneTwistHom_mul_app 𝒜 m k U a b

end Stacks.AlgebraicGeometry.ProjConeTwist

end
