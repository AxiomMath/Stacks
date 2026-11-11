module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedSectionRingMap
public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj
public import StacksFrontier.AlgebraicGeometry.TwistTensor.UniversalVeroneseSections
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading

/-!
# The graded ring map `ψ^d : S^(d) ⟶ Γ_*(U_d, 𝒪_{U_d}(d))`, into the tensor powers

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring, `X = Proj 𝒮`, `d ≥ 1` and
`U_d = ⋃_{f ∈ 𝒮 d} D₊(f)` the open of Equation 01N5. Stacks Equation 01N6 is the homomorphism
of graded rings

  `ψ^d : S^(d) ⟶ Γ_*(U_d, 𝒪_{U_d}(d)) = ⨁_{n ≥ 0} Γ(U_d, 𝒪_{U_d}(d)^{⊗ n})`

of Modules, Definition 01CV, obtained from the graded ring map `S ⟶ ⨁_k Γ(X, 𝒪_X(k))` of
Equation 01MP by restriction to `U_d` and the isomorphisms `𝒪_{U_d}(nd) ≅ 𝒪_{U_d}(d)^{⊗ n}`.
This file constructs it, with target the section ring `Stacks.GradedSections.sectionRing` of the
invertible module `𝒪_{U_d}(d)`: the direct sum over `n ≥ 0` of the global sections, read as
morphisms out of the monoidal unit, of the iterated tensor powers `𝒪_{U_d}(d)^{⊗ n}`, with the
multiplication of [Stacks, Tag 01CV].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor.tensorPowGrading`: the homogeneous
  components of the section ring `Γ_*(Y, L)`.
* `Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor.sumRingHom`: the ring map
  `⨁_n (S^(d))_n ⟶ Γ_*(Y, L)` attached to a degreewise multiplicative and unital family of
  sections of the tensor powers of an invertible module `L`.
* `Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor.psiTensor`: **the graded ring homomorphism
  `ψ^d : S^(d) ⟶ Γ_*(U_d, 𝒪_{U_d}(d))` of Stacks Equation 01N6.**

## Main results

* `Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor.secOf_toFun_zero_one`: a degreewise
  multiplicative family of sections whose degree-one values generate `L` sends `1` to the unit
  of `Γ_*(Y, L)`.
* `Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor.psiTensor_apply_homogeneous`: on a
  homogeneous element `a` of Veronese degree `n`, `ψ^d(a)` is the restriction to `U_d` of the
  global section of `𝒪_X(nd)` attached to `a`, carried to `𝒪_{U_d}(d)^{⊗ n}` by the comparison
  isomorphism `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat`, and placed in
  degree `n`.

## Implementation notes

The degreewise maps are those of
`Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple.universalVeroneseSections`, which carries
the multiplicativity across degrees. The unit law is not part of that datum; it is proved here
from generation in degree one: if `e` is the image of `1`, then `e · ψ(f) = ψ(f)` for every
`f ∈ 𝒮 d`, so the function `e` is `1` on the nonvanishing open of each `ψ(f)`, and these cover
`U_d`.

The map `Stacks.AlgebraicGeometry.ProjDegreeOpenSections.psi` is the same map with each tensor
power `𝒪_{U_d}(d)^{⊗ n}` replaced by the twist `𝒪_{U_d}(nd)`.

`Stacks.Veronese.veroneseGradingGradedRing` takes the positivity of `d`, so `psiTensor` does: the
decomposition of the Veronese subring into the pieces `𝒮 (nd)` needs `n ↦ nd` injective.

## References

* [Stacks Project, Equation 01N6](https://stacks.math.columbia.edu/tag/01N6)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Equation 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents (universalTwist)
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple (universalVeroneseSections
  universalVeroneseSections_toFun
  iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection nonvanishingOpen_psiSection)
open Stacks.AlgebraicGeometry.MorphismsIntoProj (veroneseToGrade)
open Stacks.GradedSections (powSections sectionRing mul)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.SectionProduct (globalSection)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.Veronese
open scoped DirectSum

universe u w

namespace Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### The homogeneous components of `Γ_*(Y, L)` -/

section Grading

variable {Y : Scheme.{u}} (L : Y.Modules)

/-- The degree `n` homogeneous component of the section ring `Γ_*(Y, L)`: the image of the
summand `Γ(Y, L^{⊗ n})`. -/
def tensorPowGrading (n : ℕ) : AddSubgroup (sectionRing L) :=
  (DirectSum.of (powSections L) n).range

end Grading

/-! ### A unital multiplicative family of sections is a ring map -/

section General

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] (ψ : VeroneseSections 𝒜 d L)

variable (𝒜 d) in
/-- The unit of `A`, as an element of the degree `0 · d` piece. -/
def oneZero : 𝒜 (0 * d) :=
  ⟨1, by rw [zero_mul]; exact SetLike.GradedOne.one_mem⟩

/-- The value of `ψ` at the unit, times a degree-one value, is that value scaled by the function
attached to the image of the unit. -/
private theorem pow_one_eq_smul (f : 𝒜 d) :
    ψ.pow f.2 1 =
      Stacks.SectionRingGeometric.unitScalar Y (secOf L (ψ.toFun 0 (oneZero 𝒜 d))) •
        ψ.pow f.2 1 := by
  have h : ψ.pow f.2 1 = mulSections L (ψ.toFun 0 (oneZero 𝒜 d)) (ψ.pow f.2 1) :=
    ψ.map_mul 0 1 (oneZero 𝒜 d) _ _ (one_mul _).symm
  refine h.trans ?_
  conv_lhs => rw [← globalSection_secOf L (ψ.toFun 0 (oneZero 𝒜 d)),
    ← globalSection_secOf L (ψ.pow f.2 1)]
  rw [mulSections_globalSection, Stacks.AlgebraicGeometry.GradedSectionRingMap.mul_degreeZero_one]
  exact (Stacks.SectionRingGeometric.globalSection_unitComp Y _ (secOf L (ψ.pow f.2 1))).trans
    (congrArg (Stacks.SectionRingGeometric.unitScalar Y (secOf L (ψ.toFun 0 (oneZero 𝒜 d))) • ·)
      (globalSection_secOf L (ψ.pow f.2 1)))

/-- **A degreewise multiplicative family of sections whose degree-one values generate `L` sends
`1` to the unit of `Γ_*(Y, L)`.** -/
theorem secOf_toFun_zero_one
    (hgen : (⨆ f : 𝒜 d, nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1)) = ⊤) :
    secOf L (ψ.toFun 0 (oneZero 𝒜 d)) = 𝟙 (𝟙_ Y.Modules) := by
  set r := Stacks.SectionRingGeometric.unitScalar Y (secOf L (ψ.toFun 0 (oneZero 𝒜 d)))
    with hr
  have key : ∀ (W : Y.Opens) (x : Γ(natTensorPow L 1, ⊤)), x = r • x →
      resTop (natTensorPow L 1) x W =
        Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op r • resTop (natTensorPow L 1) x W := by
    intro W x hx
    conv_lhs => rw [hx]
    exact Scheme.Modules.map_smul _ _ _ _
  have hloc : ∀ f : 𝒜 d,
      Y.presheaf.map (homOfLE (le_top :
          nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1) ≤ ⊤)).op r = 1 := fun f =>
    (ψ.ratio_eq_of_resTop_eq f.2 le_rfl (key _ _ (pow_one_eq_smul ψ f))).symm.trans
      (ψ.ratio_pow f.2 le_rfl 1)
  have hr1 : r = 1 := by
    refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf
      (fun f : 𝒜 d => nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1)) ⊤
      (fun f => homOfLE le_top) hgen.ge _ _ fun f => ?_
    refine (hloc f).trans ?_
    exact (map_one _).symm
  exact (Stacks.SectionRingGeometric.unitScalarEquiv Y).injective
    (hr1.trans (Stacks.SectionRingGeometric.unitScalar_id Y).symm)

variable (𝒜 d) in
/-- The degree `n` piece of the Veronese subring, sent to its sections of `L^{⊗ n}`. -/
def componentHom (ψ : VeroneseSections 𝒜 d L) (n : ℕ) :
    veroneseGrading 𝒜 d n →+ powSections L n :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv Y
      (natTensorPow L n)).symm.toAddMonoidHom.comp ((ψ.toFun n).comp (veroneseToGrade 𝒜 d n))

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- `componentHom` is the section of `L^{⊗ n}` attached by `ψ` to the underlying element. -/
@[simp] theorem componentHom_apply (n : ℕ) (a : veroneseGrading 𝒜 d n) :
    componentHom 𝒜 d ψ n a = secOf L (ψ.toFun n (veroneseToGrade 𝒜 d n a)) :=
  rfl

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The section of a product of honest sections is the product of the sections. -/
private theorem secOf_mulSections {n m : ℕ} (x : Γ(natTensorPow L n, ⊤))
    (y : Γ(natTensorPow L m, ⊤)) :
    secOf L (mulSections L x y) = mul (secOf L x) (secOf L y) := by
  have h := mulSections_globalSection L (secOf L x) (secOf L y)
  rw [globalSection_secOf, globalSection_secOf] at h
  rw [h, secOf_globalSection]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The component maps are multiplicative across degrees. -/
theorem componentHom_mul (n m : ℕ) (a : veroneseGrading 𝒜 d n) (b : veroneseGrading 𝒜 d m) :
    componentHom 𝒜 d ψ (n + m)
        (GradedMonoid.GMul.mul (A := fun i => (veroneseGrading 𝒜 d i : Type u)) a b) =
      mul (componentHom 𝒜 d ψ n a) (componentHom 𝒜 d ψ m b) := by
  rw [componentHom_apply, componentHom_apply, componentHom_apply,
    ψ.map_mul n m (veroneseToGrade 𝒜 d n a) (veroneseToGrade 𝒜 d m b) _ rfl,
    secOf_mulSections]

/-- **The ring map `⨁_n (A^(d))_n ⟶ Γ_*(Y, L)`** attached to a degreewise multiplicative family of
sections sending `1` to the unit. -/
def sumRingHom (h1 : secOf L (ψ.toFun 0 (oneZero 𝒜 d)) = 𝟙 (𝟙_ Y.Modules)) :
    (⨁ n : ℕ, veroneseGrading 𝒜 d n) →+* sectionRing L :=
  DirectSum.toSemiring
    (fun n => (DirectSum.of (powSections L) n).comp (componentHom 𝒜 d ψ n))
    (by
      rw [AddMonoidHom.comp_apply, DirectSum.one_def]
      exact congrArg (DirectSum.of (powSections L) 0) h1)
    (by
      intro n m a b
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        Stacks.SectionProduct.of_mul_of]
      exact congrArg (DirectSum.of (powSections L) (n + m)) (componentHom_mul ψ n m a b))

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- On a homogeneous summand `sumRingHom` is the component map. -/
theorem sumRingHom_of (h1 : secOf L (ψ.toFun 0 (oneZero 𝒜 d)) = 𝟙 (𝟙_ Y.Modules)) (n : ℕ)
    (a : veroneseGrading 𝒜 d n) :
    sumRingHom ψ h1 (DirectSum.of (fun i => (veroneseGrading 𝒜 d i : Type u)) n a) =
      DirectSum.of (powSections L) n (componentHom 𝒜 d ψ n a) :=
  DirectSum.toAddMonoid_of
    (fun n => (DirectSum.of (powSections L) n).comp (componentHom 𝒜 d ψ n)) n a

end General

/-! ### The map `ψ^d` of Equation 01N6 -/

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-- `𝒪_{U_d}(d)` is invertible. -/
instance isInvertibleModule_universalTwist :
    Stacks.Ample.IsInvertibleModule (degreeOpen 𝒮 d).toScheme (universalTwist 𝒮 d) :=
  inferInstanceAs (Stacks.Ample.IsInvertibleModule (degreeOpen 𝒮 d).toScheme
    (Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twist 𝒮 d (d : ℤ)))

/-- The map `ψ^d` sends `1` to the unit of `Γ_*(U_d, 𝒪_{U_d}(d))`. -/
theorem secOf_universalVeroneseSections_one :
    secOf (universalTwist 𝒮 d) ((universalVeroneseSections 𝒮 d).toFun 0 (oneZero 𝒮 d)) =
      𝟙 (𝟙_ (degreeOpen 𝒮 d).toScheme.Modules) :=
  secOf_toFun_zero_one (universalVeroneseSections 𝒮 d)
    ((iSup_congr fun f =>
        (nonvanishingOpen_psiSection 𝒮 (universalVeroneseSections 𝒮 d) f)).symm.trans
      (iSup_nonvanishingOpen_psiSection_universalVeroneseSections_eq_top 𝒮 d))

/-- **Stacks Equation 01N6: the graded ring homomorphism
`ψ^d : S^(d) ⟶ Γ_*(U_d, 𝒪_{U_d}(d)) = ⨁_{n ≥ 0} Γ(U_d, 𝒪_{U_d}(d)^{⊗ n})`.** The target is the
section ring of [Stacks, Tag 01CV] of the invertible module `𝒪_{U_d}(d)`, graded by the tensor
power. A homogeneous element of Veronese degree `n`, that is an element of `S_{nd}`, goes to the
restriction to `U_d` of the global section of `𝒪_X(nd)` it defines, read as a section of
`𝒪_{U_d}(d)^{⊗ n}` through the canonical isomorphism `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)`. -/
@[stacks 01N6]
def psiTensor (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    veroneseGrading 𝒮 d →+*ᵍ tensorPowGrading (universalTwist 𝒮 d) :=
  letI := veroneseGradingGradedRing 𝒮 d hd
  { __ := (sumRingHom (universalVeroneseSections 𝒮 d)
        (secOf_universalVeroneseSections_one 𝒮 d)).comp
      (DirectSum.decomposeRingEquiv (veroneseGrading 𝒮 d)).toRingHom
    map_mem := fun {n x} hx =>
      ⟨componentHom 𝒮 d (universalVeroneseSections 𝒮 d) n ⟨x, hx⟩,
        (Eq.trans
          (congrArg (sumRingHom (universalVeroneseSections 𝒮 d)
              (secOf_universalVeroneseSections_one 𝒮 d))
            (DirectSum.decompose_of_mem (veroneseGrading 𝒮 d) hx))
          (sumRingHom_of _ _ n ⟨x, hx⟩)).symm⟩ }

/-- **`ψ^d` on a homogeneous element.** On `a` of Veronese degree `n`, `ψ^d(a)` is the restriction
to `U_d` of the global section of `𝒪_X(nd)` attached to `a`, carried to `𝒪_{U_d}(d)^{⊗ n}` by the
inverse of the comparison isomorphism and placed in the degree `n` summand. -/
theorem psiTensor_apply_homogeneous (hd : 0 < d) (n : ℕ) (a : veroneseGrading 𝒮 d n) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    psiTensor 𝒮 d hd (a : veroneseSubring 𝒮 d) =
      DirectSum.of (powSections (universalTwist 𝒮 d)) n
        (secOf (universalTwist 𝒮 d)
          ((Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat 𝒮 d n).inv.val.app
            (op ⊤)
            (Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d)
              (n * d) (veroneseToGrade 𝒮 d n a)))) :=
  let := veroneseGradingGradedRing 𝒮 d hd
  Eq.trans
    (congrArg (sumRingHom (universalVeroneseSections 𝒮 d)
        (secOf_universalVeroneseSections_one 𝒮 d))
      (DirectSum.decompose_of_mem (veroneseGrading 𝒮 d) a.2))
    (sumRingHom_of _ _ n a)

end Stacks.AlgebraicGeometry.ProjDegreeOpenPsiTensor

end
