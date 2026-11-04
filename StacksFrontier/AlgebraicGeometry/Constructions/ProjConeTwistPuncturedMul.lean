module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPuncturedGlobalMap
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistUnit

/-!
# The punctured degreewise inclusion `𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` is multiplicative and unital

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L ⟶ P` be the cone attached
to the truncation algebra, with `U ⊆ L` the punctured cone. The degreewise inclusions
`𝒪_P(m) ⟶ (π|_U)_* 𝒪_U` of
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom` add up to an isomorphism of sheaves of
`𝒪_P`-modules, by
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeStructureCoproductIso`. **This file proves
that they also multiply as the grading prescribes, and that the one in degree zero carries the
unit section to the function `1`** — the ring-theoretic content of [Stacks, Tag 0EKG] on the
punctured side, which is what makes `(π|_U)_* 𝒪_U` the graded algebra
`Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra` of all integral twists and not merely
the coproduct of its homogeneous pieces.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeSections`: the ring of functions on the
  part of the punctured cone lying over an open of `P`.

## Main results

* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistAwayHom_mul` and
  `puncturedConeTwistAwayHom_one`: the local degreewise inclusion into
  `(B[1/σ f · ψ f])₀` is multiplicative and unital.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedConeTwistApp_mul` and
  `puncturedConeTwistApp_one`: **the same on sections over a standard open.**
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedPushforwardStructureSheaf_map_mul` and
  `puncturedPushforwardStructureSheaf_map_one`: restriction in the direct image of the structure
  sheaf of the punctured cone is a ring homomorphism.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_mul_app`: **the glued degreewise
  inclusion is multiplicative over every open of `P`, in every integer degree** — the `ι_mul`
  condition for the punctured cone, graded by `integerTwistAlgebra`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_one_app`: **the glued degreewise
  inclusion in degree zero carries the unit of the twist algebra to the function `1`**, over
  every open of `P`.

## Implementation notes

Because the punctured algebra is indexed by all of `ℤ`, the local statements are stated at a
`Stacks.AlgebraicGeometry.ProjTwistComparison.PositiveElem` rather than at a standard open of a
named homogeneous element, which is the form in which
`Stacks.AlgebraicGeometry.ProjConeTwist.puncturedTwistHom_app` describes the glued morphism.

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
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A}

/-- The ring of functions on the part of the punctured cone lying over an open of `P`. The
sections of `(π|_U)_* 𝒪_U` over that open are the same thing, read as a module over the sections
of `𝒪_P`. -/
abbrev puncturedConeSections (U : Opens (ProjectiveSpectrum.top 𝒜)) : Type u :=
  Γ((openUInL 𝒜).toScheme, ((openUInL 𝒜).ι ≫ pi 𝒜) ⁻¹ᵁ U)

/-! ### The local degreewise inclusion -/

/-- **The punctured degreewise inclusion `Γ(D₊(f), 𝒪_P(m)) → (B[1/σ f · ψ f])₀` is
multiplicative**, in every pair of integer degrees. -/
@[stacks 0EKG "the punctured degreewise inclusion of the sections of the twisting sheaves over \
D+(f) into the degree-zero localization of the truncation algebra at sigma f * psi f is \
multiplicative, in every pair of integer degrees"]
theorem puncturedConeTwistAwayHom_mul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    puncturedConeTwistAwayHom 𝒜 (i + j) d hf hd
        (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) =
      puncturedConeTwistAwayHom 𝒜 i d hf hd x * puncturedConeTwistAwayHom 𝒜 j d hf hd y := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  have h1 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd (i + j)
    (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)
  have h2 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd i x
  have h3 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd j y
  have h4 := coe_sectionsTwistEquivAwayGrading_mul 𝒜 hf hd i j x y
  have h0 : puncturedToLocalization 𝒜
        (puncturedConeTwistAwayHom 𝒜 i d hf hd x * puncturedConeTwistAwayHom 𝒜 j d hf hd y) =
      puncturedToLocalization 𝒜 (puncturedConeTwistAwayHom 𝒜 i d hf hd x) *
        puncturedToLocalization 𝒜 (puncturedConeTwistAwayHom 𝒜 j d hf hd y) :=
    map_mul _ _ _
  exact (h1.trans (h4.trans (congrArg₂ (· * ·) h2.symm h3.symm))).trans h0.symm

/-- **The punctured degreewise inclusion `Γ(D₊(f), 𝒪_P(0)) → (B[1/σ f · ψ f])₀` is unital.** -/
@[stacks 0EKG "the punctured degreewise inclusion of the sections of the untwisted sheaf over \
D+(f) into the degree-zero localization of the truncation algebra at sigma f * psi f carries the \
unit section to 1"]
theorem puncturedConeTwistAwayHom_one (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    puncturedConeTwistAwayHom 𝒜 0 d hf hd
        ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f))) = 1 := by
  refine puncturedToLocalization_injective 𝒜 d hf ?_
  have h1 := puncturedToLocalization_puncturedGradingEquivSectionsTwist_symm 𝒜 d hf hd 0
    ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
  have h2 := coe_sectionsTwistEquivAwayGrading_one 𝒜 hf hd
  have h3 : puncturedToLocalization 𝒜
      (1 : HomogeneousLocalization.Away (grading 𝒜) (sigmaMulPsi 𝒜 f)) = 1 := map_one _
  exact (h1.trans h2).trans h3.symm

/-- **The local punctured degreewise inclusion on sections is multiplicative**, in every pair of
integer degrees. -/
@[stacks 0EKG "the local punctured degreewise inclusion of the sections of O_P(m) into the \
functions on the punctured cone over D+(f) is multiplicative, in every pair of integer degrees"]
theorem puncturedConeTwistApp_mul (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (show puncturedConeSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
        (puncturedConeTwistApp 𝒜 (i + j) d hf hd).hom
          (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)) =
      (show puncturedConeSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
          (puncturedConeTwistApp 𝒜 i d hf hd).hom x) *
        (show puncturedConeSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
          (puncturedConeTwistApp 𝒜 j d hf hd).hom y) := by
  have h0 := puncturedConeTwistApp_apply 𝒜 (i + j) d hf hd
    (twistMulSection 𝒜 i j (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y)
  have h1 := puncturedConeTwistApp_apply 𝒜 i d hf hd x
  have h2 := puncturedConeTwistApp_apply 𝒜 j d hf hd y
  have h3 := puncturedConeTwistAwayHom_mul 𝒜 d hf hd i j x y
  rw [h0, h1, h2, h3, map_mul, map_mul]
  rfl

/-- **The local punctured degreewise inclusion in degree zero carries the unit section to the
function `1`** on the part of the punctured cone over the standard open. -/
@[stacks 0EKG "the local punctured degreewise inclusion in degree zero carries the unit section \
of the untwisted sheaf to the function 1 on the punctured cone, over a standard open"]
theorem puncturedConeTwistApp_one (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (show puncturedConeSections 𝒜 (ProjectiveSpectrum.basicOpen 𝒜 f) from
        (puncturedConeTwistApp 𝒜 0 d hf hd).hom
          ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))) = 1 := by
  have h0 := puncturedConeTwistApp_apply 𝒜 0 d hf hd
    ((twistOne 𝒜).eval (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
  have h1 := puncturedConeTwistAwayHom_one 𝒜 d hf hd
  rw [h0, h1, map_one, map_one]
  rfl

/-! ### The glued degreewise inclusion -/

/-- **The glued punctured degreewise inclusion is multiplicative over a standard open** of a
positive-degree homogeneous element. -/
theorem puncturedTwistHom_mul (p : PositiveElem 𝒜) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (positiveBasicOpen 𝒜 p)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (positiveBasicOpen 𝒜 p))) :
    (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
        (puncturedTwistHom 𝒜 (i + j)).val.app (op (positiveBasicOpen 𝒜 p))
          (twistMulSection 𝒜 i j (op (positiveBasicOpen 𝒜 p)) x y)) =
      (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
          (puncturedTwistHom 𝒜 i).val.app (op (positiveBasicOpen 𝒜 p)) x) *
        (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
          (puncturedTwistHom 𝒜 j).val.app (op (positiveBasicOpen 𝒜 p)) y) := by
  have hA := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 (i + j) p)
    (twistMulSection 𝒜 i j (op (positiveBasicOpen 𝒜 p)) x y)
  have hB := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 i p) x
  have hC := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 j p) y
  have h := puncturedConeTwistApp_mul 𝒜 (Classical.choose p.2) (Classical.choose_spec p.2).2
    (Classical.choose_spec p.2).1 i j x y
  exact hA.trans (h.trans (congrArg₂ (· * ·) hB.symm hC.symm))

/-- **The glued punctured degreewise inclusion in degree zero is unital over a standard open** of
a positive-degree homogeneous element. -/
theorem puncturedTwistHom_one (p : PositiveElem 𝒜) :
    (show puncturedConeSections 𝒜 (positiveBasicOpen 𝒜 p) from
        (puncturedTwistHom 𝒜 0).val.app (op (positiveBasicOpen 𝒜 p))
          ((twistOne 𝒜).eval (op (positiveBasicOpen 𝒜 p)))) = 1 := by
  have hA := ConcreteCategory.congr_hom (puncturedTwistHom_app 𝒜 0 p)
    ((twistOne 𝒜).eval (op (positiveBasicOpen 𝒜 p)))
  exact hA.trans (puncturedConeTwistApp_one 𝒜 (Classical.choose p.2)
    (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1)

/-- **Restriction in the direct image of the structure sheaf of the punctured cone is
multiplicative**: it is a restriction map of `𝒪_U` along the inclusion of preimages. -/
theorem puncturedPushforwardStructureSheaf_map_mul
    {V U : Opens (ProjectiveSpectrum.top 𝒜)} (h : V ≤ U)
    (s t : puncturedConeSections 𝒜 U) :
    (show puncturedConeSections 𝒜 V from
        (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
          (homOfLE h).op (s * t)) =
      (show puncturedConeSections 𝒜 V from
          (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
            (homOfLE h).op s) *
        (show puncturedConeSections 𝒜 V from
          (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
            (homOfLE h).op t) :=
  map_mul ((openUInL 𝒜).toScheme.presheaf.map
    ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE h)).op).hom s t

/-- **Restriction in the direct image of the structure sheaf of the punctured cone preserves
`1`.** -/
theorem puncturedPushforwardStructureSheaf_map_one
    {V U : Opens (ProjectiveSpectrum.top 𝒜)} (h : V ≤ U) :
    (show puncturedConeSections 𝒜 V from
        (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
          (homOfLE h).op (1 : puncturedConeSections 𝒜 U)) = 1 :=
  map_one ((openUInL 𝒜).toScheme.presheaf.map
    ((Opens.map ((openUInL 𝒜).ι ≫ pi 𝒜).base).map (homOfLE h)).op).hom

/-- A section of `(π|_U)_* 𝒪_U` over `U` is the image of `x` under `puncturedTwistHom` once this
holds after restriction to every positive standard open inside `U`. -/
private theorem puncturedTwistHom_app_eq_of_forall_positiveBasicOpen {k : ℤ}
    {U : Opens (ProjectiveSpectrum.top 𝒜)} (x : (twistingSheaf 𝒜 k).val.obj (op U))
    (z : puncturedConeSections 𝒜 U)
    (h : ∀ (p : PositiveElem 𝒜) (hle : positiveBasicOpen 𝒜 p ≤ U),
      (puncturedTwistHom 𝒜 k).val.app (op (positiveBasicOpen 𝒜 p))
          ((twistingSheaf 𝒜 k).val.map (homOfLE hle).op x) =
        (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)).val.map
          (homOfLE hle).op z) :
    (puncturedTwistHom 𝒜 k).val.app (op U) x = z := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis
    (Stacks.Morphisms.pushforwardStructureSheaf ((openUInL 𝒜).ι ≫ pi 𝒜)) (positiveBasicOpen 𝒜)
    (isBasis_positiveBasicOpen 𝒜) _ _ fun p hle => ?_
  exact (PresheafOfModules.naturality_apply (puncturedTwistHom 𝒜 k).val
    (homOfLE hle).op x).symm.trans (h p hle)

/-- **The inclusions of the homogeneous pieces of the algebra of all integral twists in
`(π|_U)_* 𝒪_U` multiply as the grading prescribes**, over every open of `P` and in every pair of
integer degrees. This is the `ι_mul` condition of `AlgebraicGeometry.AbstractCone` for the
punctured cone of the truncation algebra, graded by
`Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra`. -/
@[stacks 0EKG "the inclusions of the homogeneous pieces of the integral twist algebra in \
(pi|_U)_* O_U are multiplicative, over every open of P and in every pair of integer degrees, for \
the punctured cone of the truncation algebra"]
theorem puncturedTwistHom_mul_app (i j : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (a : (twistingSheaf 𝒜 i).val.obj (op U)) (b : (twistingSheaf 𝒜 j).val.obj (op U)) :
    (show puncturedConeSections 𝒜 U from
        (puncturedTwistHom 𝒜 (i + j)).val.app (op U)
          ((twistMul 𝒜 i j).app (op U) a b)) =
      (show puncturedConeSections 𝒜 U from (puncturedTwistHom 𝒜 i).val.app (op U) a) *
        (show puncturedConeSections 𝒜 U from (puncturedTwistHom 𝒜 j).val.app (op U) b) := by
  refine puncturedTwistHom_app_eq_of_forall_positiveBasicOpen 𝒜 _ _ fun p hle => ?_
  have hbil := (twistMul 𝒜 i j).naturality (homOfLE hle).op a b
  have hRa := PresheafOfModules.naturality_apply (puncturedTwistHom 𝒜 i).val (homOfLE hle).op a
  have hRb := PresheafOfModules.naturality_apply (puncturedTwistHom 𝒜 j).val (homOfLE hle).op b
  have hring := puncturedPushforwardStructureSheaf_map_mul 𝒜 hle
    ((puncturedTwistHom 𝒜 i).val.app (op U) a) ((puncturedTwistHom 𝒜 j).val.app (op U) b)
  have hloc := puncturedTwistHom_mul 𝒜 p i j
    ((twistingSheaf 𝒜 i).val.map (homOfLE hle).op a)
    ((twistingSheaf 𝒜 j).val.map (homOfLE hle).op b)
  refine Eq.trans ?_ hring.symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) hRa hRb)
  exact (congrArg _ hbil).trans hloc

/-- **The inclusion of the degree-zero piece of the algebra of all integral twists carries the
unit of that algebra to the function `1`** on the punctured cone, over every open of `P`. -/
@[stacks 0EKG "the inclusion of the degree-zero piece of the integral twist algebra carries the \
unit of the algebra to the function 1 on the punctured cone, over every open of P"]
theorem puncturedTwistHom_one_app (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (show puncturedConeSections 𝒜 U from
        (puncturedTwistHom 𝒜 0).val.app (op U) ((twistOne 𝒜).eval (op U))) = 1 := by
  refine puncturedTwistHom_app_eq_of_forall_positiveBasicOpen 𝒜 _ _ fun p hle => ?_
  exact (congrArg _ (rfl : (twistingSheaf 𝒜 0).val.map (homOfLE hle).op ((twistOne 𝒜).eval (op U))
    = (twistOne 𝒜).eval (op (positiveBasicOpen 𝒜 p)))).trans
    ((puncturedTwistHom_one 𝒜 p).trans (puncturedPushforwardStructureSheaf_map_one 𝒜 hle).symm)

end Stacks.AlgebraicGeometry.ProjConeTwist

end
