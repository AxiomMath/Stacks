module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGroupGaloisModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupVanishingAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeTwoCocycles

/-!
# The derived-functor vanishing of the cohomology of `𝐆_a` over a field

Let `Ω/K` be a Galois extension.  The additive group of `Ω` has vanishing continuous cohomology
in degrees one and two, and — when `Ω` has characteristic zero — in every positive degree.  Fed
through the comparison of [Stacks, Tag 03QU] part (3) at `𝐆_a`, this gives the corresponding
vanishing of the étale cohomology of `𝐆_a` over the spectrum of a field.

The two low degrees are the cochain statements
`Stacks.GaloisCohomology.exists_dZero_eq_additive` and
`Stacks.GaloisCohomology.exists_dOne_eq_additive` — the normal basis theorem at a finite Galois
level, inflated — read through the comparisons between cocycles and derived functors,
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary` and its
degree-two sibling.  The characteristic-zero statement is [Stacks, Tag 0DV3] part (2): the
additive group of a field of characteristic zero is a rational vector space, and the
positive-degree continuous cohomology of a profinite group with such coefficients vanishes.

## Main results

* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_addLift_one` and
  `…_addLift_two`: **`H ¹(Gal(Ω/K), Ω) = 0` and `H ²(Gal(Ω/K), Ω) = 0`** for the
  derived-functor groups, for an arbitrary Galois extension and at an arbitrary coefficient
  universe.
* `Stacks.GaloisCohomology.isZero_continuousGroupCohomology_addLift_of_charZero`:
  **`H ^q(Gal(Ω/K), Ω) = 0` for every `q ≥ 1` when `Ω` has characteristic zero.**
* `AlgebraicGeometry.subsingleton_sheafH_additiveSheaf_one` and `…_two`:
  **`H ¹_étale(Spec K, 𝐆_a) = 0` and `H ²_étale(Spec K, 𝐆_a) = 0`** for an arbitrary field,
  with no choice of big étale site or geometric point in the statement.
* `AlgebraicGeometry.subsingleton_sheafH_additiveSheaf_of_charZero`:
  **`H ^q_étale(Spec K, 𝐆_a) = 0` for every `q ≥ 1` when `K` has characteristic zero.**

## Implementation notes

This is the additive transcription of `…GaloisCohomology.MultiplicativeGroupVanishingUniverseLift`
and of the assembly in `…GaloisCohomology.MultiplicativeGroupVanishingAllDegrees`, and follows
them step for step: each statement is proved at the raised module
`Stacks.GaloisCohomology.addContinuousGModuleLift` rather than transported to it, the two
degree-wise criteria being polymorphic in the coefficient universe and the cochain hypotheses
transporting along `ULift.down`.

**Why the unconditional degree range stops at two.**  Past degree two this library reaches a
vanishing statement in one of two ways, and neither is available for the additive group.  The
route of `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_forall_isAddTorsion` asks
for the vanishing in degrees `q ≥ 2` for *every* torsion discrete module, which for a Galois
group is a hypothesis on the field, supplied for `𝐆_m` by the Brauer-group assumption of
[Stacks, Tag 03R8] and by nothing here.  The route of [Stacks, Tag 0DV3] part (2) asks for
rational coefficients, which is exactly the characteristic-zero case recorded below.  In
characteristic `p` the additive group is killed by `p`, so neither applies, and the classical
argument — the cohomology of a profinite group is the colimit of the cohomology of its finite
quotients, at each of which the normal basis theorem makes the coefficients an induced module —
has no counterpart in this library: continuous cohomology here is a right derived functor and
the only comparisons with cochains are the degree-one and degree-two ones used above.

**The characteristic-zero hypothesis is on the extension, not on the base.**  The module whose
cohomology is taken is the additive group of `Ω`, so `CharZero Ω` is what the rational
vector-space structure needs; over `Spec K` it is derived from `CharZero K` along the two field
maps that produce the separable closure of the residue field.

## References

* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): the comparison whose
  part (3) at `𝐆_a` turns these into étale statements.
* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3): part (2), the
  characteristic-zero input.
* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the vanishing of the
  Galois cohomology of the additive group, of which the two low degrees are the cochain form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.GaloisCohomology

/-! ### Degrees one and two, for an arbitrary Galois extension -/

/-- **`H ¹(Gal(Ω/K), Ω) = 0`** for the derived-functor groups, at an arbitrary coefficient
universe.  This is the cochain statement
`Stacks.GaloisCohomology.exists_dZero_eq_additive` read through the degree-one comparison
between cocycles and the derived functor. -/
theorem isZero_continuousGroupCohomology_addLift_one.{s, t} (K Ω : Type s) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] :
    IsZero (continuousGroupCohomology.{s, t} Gal(Ω/K) 1
      (addContinuousGModuleLift.{s, t} K Ω)) := by
  refine Stacks.GroupCohomology.isZero_continuousGroupCohomology_one_of_forall_isCoboundary
    (addContinuousGModuleLift.{s, t} K Ω) ?_
  intro c hcloc hccoc
  obtain ⟨x, hx⟩ := exists_dZero_eq_additive (K := K) (Ω := Ω) (fun g ↦ (c g).down)
    (hcloc.comp fun a ↦ a.down) fun g₁ g₂ ↦ congrArg ULift.down (hccoc g₁ g₂)
  exact ⟨ULift.up x, fun g ↦ ULift.down_injective (congrFun hx g)⟩

/-- **`H ²(Gal(Ω/K), Ω) = 0`** for the derived-functor groups, at an arbitrary coefficient
universe.  This is the cochain statement `Stacks.GaloisCohomology.exists_dOne_eq_additive` read
through the degree-two comparison between cocycles and the derived functor; the trivializing
`1`-cochain produced there is locally constant, which is what that comparison asks for. -/
theorem isZero_continuousGroupCohomology_addLift_two.{s, t} (K Ω : Type s) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] :
    IsZero (continuousGroupCohomology.{s, t} Gal(Ω/K) 2
      (addContinuousGModuleLift.{s, t} K Ω)) := by
  refine Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary
    (addContinuousGModuleLift.{s, t} K Ω) ?_
  intro d hdloc hdcoc
  obtain ⟨x, hxloc, hx⟩ := exists_dOne_eq_additive (K := K) (Ω := Ω) (fun p ↦ (d p).down)
    (hdloc.comp fun a ↦ a.down) fun g₁ g₂ g₃ ↦ congrArg ULift.down (hdcoc g₁ g₂ g₃)
  exact ⟨fun g ↦ ULift.up (x g), hxloc.comp ULift.up,
    fun g₁ g₂ ↦ ULift.down_injective (congrFun hx (g₁, g₂))⟩

/-! ### Every positive degree in characteristic zero -/

/-- **`H ^q(Gal(Ω/K), Ω) = 0` for every `q ≥ 1` when `Ω` has characteristic zero.**  The additive
group of a field of characteristic zero is a rational vector space, and the positive-degree
continuous cohomology of a profinite group with rational coefficients vanishes, which is
[Stacks, Tag 0DV3] part (2). -/
theorem isZero_continuousGroupCohomology_addLift_of_charZero.{s, t} (K Ω : Type s) [Field K]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω] [CharZero Ω] (q : ℕ) (hq : 0 < q) :
    IsZero (continuousGroupCohomology.{s, t} Gal(Ω/K) q
      (addContinuousGModuleLift.{s, t} K Ω)) := by
  let : Module ℚ ((addContinuousGModuleLift.{s, t} K Ω).1.1.V) :=
    inferInstanceAs (Module ℚ (ULift.{t} Ω))
  exact isZero_continuousGroupCohomology_of_module_rat.{s, t}
    Gal(Ω/K) (isProfiniteTop_galGroup K Ω) q hq (addContinuousGModuleLift.{s, t} K Ω)

end Stacks.GaloisCohomology

namespace AlgebraicGeometry

open Stacks.GaloisCohomology

universe u

attribute [local instance] GeometricPoint.residueFieldAlgebra

attribute [local instance]
  preservesFilteredColimitsOfSize_forget_addCommGrpCat
  isGrothendieckAbelian_sheaf_smallEtale_pinnedCoefficients

section Comparison

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

include B hK sbar in
/-- **`H ¹_étale(Spec K, 𝐆_a) = 0` for an arbitrary field**, with no hypothesis.  This is the
additive analogue of Hilbert's theorem 90, read through Tag 03QU part (3) at `𝐆_a`. -/
theorem subsingleton_additiveSheafH_one :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) 1) :=
  (subsingleton_additiveSheafH_iff_isZero B K hK sbar 1).mpr
    (isZero_continuousGroupCohomology_addLift_one.{u, u + 1} _ _)

include B hK sbar in
/-- **`H ²_étale(Spec K, 𝐆_a) = 0` for an arbitrary field**, with no hypothesis. -/
theorem subsingleton_additiveSheafH_two :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) 2) :=
  (subsingleton_additiveSheafH_iff_isZero B K hK sbar 2).mpr
    (isZero_continuousGroupCohomology_addLift_two.{u, u + 1} _ _)

/-- **The separable closure at a geometric point of the spectrum of a field of characteristic
zero has characteristic zero.**  The residue field at the image of the point is a copy of `K` by
`AlgebraicGeometry.residueFieldSpecRingEquiv`, and the separable closure is an extension of
it. -/
theorem charZero_separableClosure [CharZero K] :
    CharZero ↥(GeometricPoint.separableClosure sbar) := by
  let : Algebra K ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) :=
    (residueFieldSpecRingEquiv K (sbar.hom default)).toRingHom.toAlgebra
  have : CharZero ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default)) :=
    charZero_of_injective_algebraMap
      (residueFieldSpecRingEquiv K (sbar.hom default)).injective
  exact charZero_of_injective_algebraMap
    (algebraMap ↥((Spec (CommRingCat.of K)).residueField (sbar.hom default))
      ↥(GeometricPoint.separableClosure sbar)).injective

include B hK sbar in
/-- **`H ^q_étale(Spec K, 𝐆_a) = 0` in every degree `q ≥ 1` when `K` has characteristic zero.**
This is [Stacks, Tag 0DV3] part (2) — the vanishing of the positive-degree continuous cohomology
of a profinite group with rational coefficients — read through Tag 03QU part (3) at `𝐆_a`. -/
theorem subsingleton_additiveSheafH_of_charZero [CharZero K] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q) :=
  have := charZero_separableClosure K sbar
  (subsingleton_additiveSheafH_iff_isZero B K hK sbar q).mpr
    (isZero_continuousGroupCohomology_addLift_of_charZero.{u, u + 1} _ _ q hq)

end Comparison

/-! ### The vanishing statements with no choice of site or geometric point -/

section Absolute

variable (K : Type u) [Field K]

/-- **`H ¹_étale(Spec K, 𝐆_a) = 0` for an arbitrary field**, with no choice of big étale site or
geometric point in the statement. -/
theorem subsingleton_sheafH_additiveSheaf_one :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) 1) :=
  subsingleton_additiveSheafH_one (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K)

/-- **`H ²_étale(Spec K, 𝐆_a) = 0` for an arbitrary field**, with no choice of big étale site or
geometric point in the statement. -/
theorem subsingleton_sheafH_additiveSheaf_two :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) 2) :=
  subsingleton_additiveSheafH_two (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K)

/-- **`H ^q_étale(Spec K, 𝐆_a) = 0` in every degree `q ≥ 1` when `K` has characteristic zero**,
with no choice of big étale site or geometric point in the statement.  Together with
`AlgebraicGeometry.isZero_hgroup_structureSheaf_spec_field` and the comparison
`AlgebraicGeometry.additiveSheafHAddEquivContinuousGroupCohomology` this is the whole additive
chain of equalities of [Stacks, Tag 03QV] for a field of characteristic zero. -/
theorem subsingleton_sheafH_additiveSheaf_of_charZero [CharZero K] (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.ArtinSchreier.additiveSheaf.{u, u + 1} (Spec (.of K))) q) :=
  subsingleton_additiveSheafH_of_charZero (BigEtaleSite.containing (Spec (.of K))) K
    (BigEtaleSite.contains_containing _) (GeometricPoint.ofAlgebraicClosure K) q hq

end Absolute

end AlgebraicGeometry

end
