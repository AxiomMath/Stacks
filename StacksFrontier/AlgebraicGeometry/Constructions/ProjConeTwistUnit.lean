module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistGlobalMul

/-!
# The degreewise inclusion carries the unit of the twist algebra to `1`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra. The algebra of nonnegative twists has the constant section `1` of the
untwisted sheaf as its distinguished degree-zero unit, which is
`Stacks.AlgebraicGeometry.ProjConeTwist.twistOne`. **This file proves that the degreewise
inclusion in degree zero carries it to the function `1` on the cone**, over every open of `P`.

Together with `Stacks.AlgebraicGeometry.ProjConeTwist.coneIota_mul` this says that the inclusions
of the homogeneous pieces assemble into a *unital* ring homomorphism out of the ungraded
realization of the twist algebra, which is what [Stacks, Tag 0EKG] asserts about `π_* 𝒪_L` beyond
the identification of its underlying sheaf of modules.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.moduleToFiber_one`: for the regular module the
  comparison with a fibre is unital.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coe_sectionsTwistEquivAwayGrading_one`: the
  standard-open identification carries the unit section of `𝒪_P(0)` to `1`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistAwayHom_one` and
  `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_one`: the local degreewise inclusion in
  degree zero is unital.
* `Stacks.AlgebraicGeometry.ProjConeTwist.pushforwardStructureSheaf_map_one`: restriction in the
  direct image preserves `1`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneIota_one`: **the inclusion of the degree-zero piece
  carries the unit of the twist algebra to `1`**, over every open of `P`.

## Implementation notes

The route is the one of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjConeTwistStandardOpenMul.lean`:
the unit section is the constant fraction `1`, so the standard-open identification sends it to
`1 ∈ A[1/f]`, which is checked by applying the comparison
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroToSection` out of the degree-zero fractions
and using that a fibre map is unital; injectivity of that comparison transports the identity
back. The passage from a standard open to an arbitrary one is separatedness, exactly as for the
multiplicativity: the unit section of `𝒪_P(0)` restricts to the unit section, and restriction in
the direct image preserves `1`.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjTwistComparison

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The unit of a localization of a ring is the fraction `1 / t` for any denominator `t` equal
to `1`. -/
private theorem one_eq_mk_one {R : Type*} [CommRing R] {s : Submonoid R} (t : s)
    (ht : (t : R) = 1) : (1 : LocalizedModule s R) = LocalizedModule.mk 1 t :=
  OreLocalization.one_def.trans (congrArg (LocalizedModule.mk 1) (Subtype.ext ht.symm))

/-- **For the regular module the comparison of `A[1/f]` with a fibre is unital.** -/
theorem moduleToFiber_one (f : S) (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    moduleToFiber (M := S) 𝒜 f x 1 = 1 := by
  rw [one_eq_mk_one (1 : Submonoid.powers f) rfl, moduleToFiber_mk,
    one_eq_mk_one (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) rfl]
  rfl

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- The constant fraction `1` is a degree-zero fraction of the untwisted module. -/
theorem one_mem_degreeZeroLocalization_twistGrading {d : ℕ} (hf : f ∈ 𝒜 d) :
    (1 : LocalizedModule.Away f A) ∈
      GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 0) f := by
  rw [one_eq_mk_one (⟨f ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers f) (pow_zero f)]
  refine Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree 𝒜
    (twistGrading (S := A) 𝒜 0) hf 0 1 ?_
  exact mem_twistGrading_of_mem 𝒜 (by simp) (SetLike.one_mem_graded 𝒜)

/-- **The standard-open identification carries the unit section of `𝒪_P(0)` to `1`.** -/
@[stacks 0EKG "the standard-open identification of the sections of the untwisted sheaf with the \
degree-zero fractions carries the unit section to 1"]
theorem coe_sectionsTwistEquivAwayGrading_one {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd 0
          ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
        LocalizedModule.Away f A)) = 1 := by
  have hmem := one_mem_degreeZeroLocalization_twistGrading 𝒜 hf
  have key : degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 0) f
        ⟨(1 : LocalizedModule.Away f A), hmem⟩ =
      (twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)) := by
    refine twistSection_ext 𝒜 fun p => ?_
    change moduleToFiber (M := A) 𝒜 f p (1 : LocalizedModule.Away f A) = 1
    exact moduleToFiber_one 𝒜 f p
  have hinj : associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 0) hf hd
        ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f))) =
      ⟨(1 : LocalizedModule.Away f A), hmem⟩ :=
    degreeZeroToSection_injective 𝒜 (twistGrading (S := A) 𝒜 0) hf hd
      ((degreeZeroToSection_associatedModuleSheafStandardOpenEquiv 𝒜
        (twistGrading (S := A) 𝒜 0) hf hd _).trans key.symm)
  exact congrArg Subtype.val hinj

/-- **The degreewise inclusion `Γ(D₊(f), 𝒪_P(0)) → (B[1/ψ f])₀` is unital.** -/
@[stacks 0EKG "the degreewise inclusion of the sections of the untwisted sheaf over D+(f) into \
the degree-zero localization of the truncation algebra carries the unit section to 1"]
theorem coneTwistAwayHom_one (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    coneTwistAwayHom 𝒜 0 d hf hd ((twistOne 𝒜).eval
        (op (ProjectiveSpectrum.basicOpen 𝒜 f))) = 1 := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  have h1 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd 0
    ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
  have h2 := coe_sectionsTwistEquivAwayGrading_one 𝒜 hf hd
  have h3 : awayToLocalization 𝒜 (1 : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) = 1 :=
    map_one _
  exact (h1.trans h2).trans h3.symm

/-- **The local degreewise inclusion in degree zero carries the unit section to the function
`1`** on the part of the cone over the standard open. -/
@[stacks 0EKG "the local degreewise inclusion in degree zero carries the unit section of the \
untwisted sheaf to the function 1 on the cone, over a standard open"]
theorem coneTwistApp_one (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (show coneSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
        (coneTwistApp 𝒜 0 d hf hd).hom
          ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) = 1 := by
  have h0 := coneTwistApp_apply 𝒜 0 d hf hd
    ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
  have h1 := coneTwistAwayHom_one 𝒜 d hf hd
  rw [h0, h1, map_one, map_one]
  rfl

/-- **The glued degreewise inclusion in degree zero is unital over a standard open** of a
positive-degree homogeneous element. -/
theorem coneTwistHom_one {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (show coneSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
        (coneTwistHom 𝒜 0).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f))
          ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) = 1 := by
  have hA := ConcreteCategory.congr_hom (coneTwistHom_app 𝒜 0 hf hd)
    ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
  exact hA.trans (coneTwistApp_one 𝒜 d hf hd)

/-- **Restriction in the direct image of a structure sheaf preserves `1`.** -/
theorem pushforwardStructureSheaf_map_one {V U : Opens (ProjectiveSpectrum.top 𝒜)} (h : V ≤ U) :
    (show coneSections 𝒜 V from
        (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE h).op
          (1 : coneSections 𝒜 U)) = 1 :=
  map_one ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
    ((Opens.map (pi 𝒜).base).map (homOfLE h)).op).hom

/-- **The inclusion of the degree-zero piece of the algebra of nonnegative twists carries the
unit of that algebra to the function `1`**, over every open of `P`. With
`Stacks.AlgebraicGeometry.ProjConeTwist.coneIota_mul` this exhibits the inclusions as a unital
ring homomorphism out of the ungraded realization of the twist algebra. -/
@[stacks 0EKG "the inclusion of the degree-zero piece of the nonnegative twist algebra carries \
the unit of the algebra to the function 1, over every open of P, for the truncation cone"]
theorem coneIota_one (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (show coneSections 𝒜 U from
        (coneIota 𝒜 0).val.app (op U) ((twistOne 𝒜).eval (op U))) = 1 := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)) (positiveBasicOpen 𝒜)
    (isBasis_positiveBasicOpen 𝒜) _ _ fun p hle => ?_
  have hd : 0 < Classical.choose p.2 := (Classical.choose_spec p.2).1
  have hf : p.1 ∈ 𝒜 (Classical.choose p.2) := (Classical.choose_spec p.2).2
  have hL := PresheafOfModules.naturality_apply (coneTwistHom 𝒜 0).val (homOfLE hle).op
    ((twistOne 𝒜).eval (op U))
  have hres : (twistingSheaf 𝒜 0).val.map (homOfLE hle).op ((twistOne 𝒜).eval (op U)) =
      (twistOne 𝒜).eval (op (positiveBasicOpen 𝒜 p)) := rfl
  have hone := coneTwistHom_one 𝒜 hf hd
  have hring := pushforwardStructureSheaf_map_one 𝒜 hle
  refine hL.symm.trans (Eq.trans ?_ hring.symm)
  exact (congrArg _ hres).trans hone

end Stacks.AlgebraicGeometry.ProjConeTwist

end
