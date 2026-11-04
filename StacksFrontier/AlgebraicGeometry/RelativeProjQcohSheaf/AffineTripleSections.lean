module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleDegreeZeroScalar
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionComponent
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTwisting
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineVeronese
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential

/-!
# A triple over an affine base, as the linear data a twisting is recovered from

Let `S` be an **affine** scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN),
`A = Γ(S, 𝒜)` its graded ring of global sections, `d ≥ 1`, `T` a test scheme and `L` an
invertible `𝒪_T`-module. A *triple* of Section 01N4 over `T` is such an `L` together with a graded
map `ψ : A^{(d)} ⟶ Γ_*(T, L)` whose degree-`d` values generate `L`.

To a triple over an affine base this file attaches the morphism `f : T ⟶ S` determined by the
composite ring map `Γ(S, 𝒪_S) → A_0 → Γ(T, 𝒪_T)` through [Stacks, Tag 01I1]; for each `i : ℤ`, a
`Γ(S, 𝒪_S)`-linear map `Γ(𝒜_{id}, S) ⟶ Γ(f_*L^{⊗ i}, S)`, the scalars acting on the target
through `f^♯`, the family being multiplicative across degrees and unital; and the twisting
`f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` these maps determine.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.structureHom`: the
  morphism `T ⟶ S` of the quadruple attached to a triple.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.sectionsMap`: the
  degreewise `Γ(S, 𝒪_S)`-linear maps of a triple, for the nonnegative degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.sectionsMapInt`: the same
  family over all of `ℤ`, zero in the negative degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.twisting`: the twisting of
  a triple over an affine base.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.structureHom_appTop`: the
  recovered morphism induces the degree-zero ring map of the triple on global sections.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.sectionsMap_apply`: the
  degreewise map is the value of `ψ` on the corresponding element of the internal grading, read on
  the integral tensor power through the comparison of [Stacks, Tag 01CU].
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.sections_eq_zero_of_neg`:
  for `d > 0` a negative Veronese degree of `𝒜` has no nonzero global section.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.laurentMul_sectionsMapInt`:
  the family is multiplicative across degrees.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections.sectionsMapInt_algebraOne`:
  the family carries the unit of `𝒜^{(d)}` to the unit of the Laurent algebra.

## Implementation notes

The source of the degree-`n` map is spelled as the global sections of a homogeneous piece of
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.situationAlgebra`, as
`Stacks.AlgebraicGeometry.AffineTwisting.ofSections` requires; it is the module
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces` of degree-`nd`
homogeneous sections definitionally
(`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.sectionPieces_eq_globalSectionHom_domain`). The
target, the global sections of `f_*L^{⊗ n}`, is that of `L^{⊗ n}` definitionally
(`Stacks.AlgebraicGeometry.AffineHomRecovery.pushforward_sectionsTop_eq`).

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjTripleStructureMorphism (degreeZeroHom unitGlobal)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {T S : Scheme.{u}} (B : SheafGradedAlgebra S) {d : ℕ} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : VeroneseSections (B.grading (⊤ : S.Opens)) d L)
  (hgen : (⨆ g : B.grading (⊤ : S.Opens) d,
    nonvanishingOpen T L (psiSection (B.grading (⊤ : S.Opens)) ψ g)) = ⊤)

/-- **The structure map `R → A_0` of the graded `R`-algebra `A = Γ(S, 𝒜)`**, `R = Γ(S, 𝒪_S)`,
as a morphism of `CommRingCat`: the degree-zero scalars of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.gradeZeroHom`. -/
def structureRingHom : Γ(S, ⊤) ⟶ CommRingCat.of (B.grading (⊤ : S.Opens) 0) :=
  CommRingCat.ofHom (B.gradeZeroHom ⊤)

include hgen

/-- **The unit axiom of a triple's graded ring map**: if the degree-`d` values of `ψ` generate
`L`, then `ψ` sends `1` to the unit global section `unitGlobal L`. -/
theorem toFun_zero_eq_unitGlobal (a : B.grading (⊤ : S.Opens) (0 * d))
    (ha : (a : B.sectionRing (⊤ : S.Opens)) = 1) : ψ.toFun 0 a = unitGlobal L :=
  Stacks.AlgebraicGeometry.ProjTripleUnitSection.toFun_zero_eq_unitGlobal
    (B.grading (⊤ : S.Opens)) ψ hgen a ha

/-- **The morphism `T ⟶ S` of the quadruple attached to a triple.** It is the morphism that the
composite ring map `Γ(S, 𝒪_S) → A_0 → Γ(T, 𝒪_T)` — the structure map of the graded algebra
followed by the degree-zero part of `ψ` — determines through the affine adjunction of [Stacks, Tag
01I1]. -/
def structureHom [IsAffine S] : T ⟶ S :=
  ProjTripleDegreeZeroScalar.structureMorphism (B.grading (⊤ : S.Opens)) ψ
    (toFun_zero_eq_unitGlobal B ψ hgen) (structureRingHom B)

/-- **The recovered morphism induces, on global sections, the structure map of the graded algebra
followed by the degree-zero ring map of the triple.** By [Stacks, Tag 01I1] this characterises
it. -/
theorem structureHom_appTop [IsAffine S] :
    (structureHom B ψ hgen).appTop
      = structureRingHom B ≫ CommRingCat.ofHom
          (degreeZeroHom (B.grading (⊤ : S.Opens)) ψ (toFun_zero_eq_unitGlobal B ψ hgen)) :=
  ProjTripleDegreeZeroScalar.structureMorphism_appTop _ _ _ _

/-! ### The degreewise linear maps -/

/-- **The degreewise `Γ(S, 𝒪_S)`-linear maps of a triple over an affine base**, for the
nonnegative degrees. In degree `n` this sends a homogeneous section of `𝒜_{nd}` over `S` to the
value of `ψ` on the element of the internal grading it names, read as a global section of the
integral tensor power `L^{⊗ n}` of [Stacks, Tag 01CU] rather than of the iterated one. -/
def sectionsMap [IsAffine S] (n : ℕ) :
    Γ(AffineTwisting.pieceMod (situationAlgebra B) ((n : ℤ) * (d : ℤ)), ⊤) →ₗ[Γ(S, ⊤)]
      AffineTwisting.laurentSections (structureHom B ψ hgen) L (n : ℤ) where
  toFun y := (powCompare L n).hom.app ⊤ (ψ.toFun n (B.ofGrading ⊤ (n * d) y))
  map_add' y z :=
    (congrArg ((powCompare L n).hom.app ⊤)
      (map_add ((ψ.toFun n).comp (B.ofGrading ⊤ (n * d))) y z)).trans (map_add _ _ _)
  map_smul' r y := by
    have key : ψ.toFun n (B.ofGrading ⊤ (n * d) (r • y))
        = (structureHom B ψ hgen).appTop r • ψ.toFun n (B.ofGrading ⊤ (n * d) y) :=
      ProjTripleDegreeZeroScalar.toFun_mul_appTop (B.grading (⊤ : S.Opens)) ψ
        (toFun_zero_eq_unitGlobal B ψ hgen) (structureRingHom B) n r
        (B.ofGrading ⊤ (n * d) y) (B.ofGrading ⊤ (n * d) (r • y))
        (B.coe_ofGrading_smul ⊤ r y)
    exact (congrArg ((powCompare L n).hom.app ⊤) key).trans
      ((Scheme.Modules.Hom.app_smul (powCompare L n).hom _ _).trans rfl)

/-- The degree-`n` map `sectionsMap` sends `y` to the value of `ψ` on the element of the internal
grading `y` names, read on the integral tensor power through `powCompare`. -/
@[simp]
theorem sectionsMap_apply [IsAffine S] (n : ℕ)
    (y : Γ(AffineTwisting.pieceMod (situationAlgebra B) ((n : ℤ) * (d : ℤ)), ⊤)) :
    sectionsMap B ψ hgen n y
      = (powCompare L n).hom.app ⊤ (ψ.toFun n (B.ofGrading ⊤ (n * d) y)) :=
  rfl

/-! ### The negative degrees, and the family over `ℤ` -/

omit hgen in
/-- **The negative Veronese degrees of `𝒜` have no nonzero global sections**: for `d > 0` and
`i < 0`, every global section of `𝒜_{id}` is zero. -/
theorem sections_eq_zero_of_neg (hd : 0 < d) {i : ℤ} (hi : i < 0)
    (y : Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (d : ℤ)), ⊤)) : y = 0 :=
  Stacks.SheafOfModules.section_eq_zero_of_isZero
    (B.negative_isZero (i * (d : ℤ)) (mul_neg_of_neg_of_pos hi (by exact_mod_cast hd)))
    (op (⊤ : Opens S.toRingedSpace.carrier)) y

/-- **The degreewise `Γ(S, 𝒪_S)`-linear maps of a triple, over all of `ℤ`.** In a nonnegative
degree this is `sectionsMap`; in a negative degree it is the zero map. -/
def sectionsMapInt [IsAffine S] : ∀ i : ℤ,
    Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (d : ℤ)), ⊤) →ₗ[Γ(S, ⊤)]
      AffineTwisting.laurentSections (structureHom B ψ hgen) L i
  | .ofNat n => sectionsMap B ψ hgen n
  | .negSucc _ => 0

/-- In a nonnegative degree `n`, `sectionsMapInt` is `sectionsMap` in degree `n`. -/
@[simp]
theorem sectionsMapInt_natCast [IsAffine S] (n : ℕ) :
    sectionsMapInt B ψ hgen (n : ℤ) = sectionsMap B ψ hgen n :=
  rfl

/-- **In a negative degree the family is the zero map.** -/
theorem sectionsMapInt_eq_zero_of_neg [IsAffine S] (hd : 0 < d) {i : ℤ} (hi : i < 0) :
    sectionsMapInt B ψ hgen i = 0 :=
  LinearMap.ext fun y => by
    rw [sections_eq_zero_of_neg B hd hi y, map_zero, LinearMap.zero_apply]

/-! ### Multiplicativity across degrees -/

omit hgen in
/-- **The summand inclusion absorbs the Veronese degree transport.** Transporting a homogeneous
section along an equality of degrees and then including it as a summand is including it in the
original degree. -/
theorem of_eqToHom_piece {i j : ℕ} (hij : i = j)
    (p : (situationAlgebra B).piece ((i : ℕ) : ℤ) = (situationAlgebra B).piece ((j : ℕ) : ℤ))
    (w : B.sectionPieces ⊤ i) :
    DirectSum.of (B.sectionPieces ⊤) j
        ((eqToHom p).val.app (op (⊤ : Opens S.toRingedSpace.carrier)) w)
      = DirectSum.of (B.sectionPieces ⊤) i w := by
  subst hij
  rw [eqToHom_refl]
  rfl

omit hgen in
/-- **The multiplication of the `d`-th Veronese regrading of `𝒜` on global sections is the
product of the graded ring `A = Γ(S, 𝒜)`.** -/
theorem coe_ofGrading_algebraMul (n m : ℕ)
    (s : Γ(AffineTwisting.pieceMod (situationAlgebra B) ((n : ℤ) * (d : ℤ)), ⊤))
    (t : Γ(AffineTwisting.pieceMod (situationAlgebra B) ((m : ℤ) * (d : ℤ)), ⊤)) :
    ((B.ofGrading ⊤ ((n + m) * d)
          (AffineTwisting.algebraMul (situationAlgebra B) (d : ℤ) (n : ℤ) (m : ℤ) s t) :
        B.grading ⊤ ((n + m) * d)) : B.sectionRing ⊤)
      = ((B.ofGrading ⊤ (n * d) s : B.grading ⊤ (n * d)) : B.sectionRing ⊤)
        * ((B.ofGrading ⊤ (m * d) t : B.grading ⊤ (m * d)) : B.sectionRing ⊤) :=
  (of_eqToHom_piece B (add_mul n m d).symm _ _).trans
    (DirectSum.of_mul_of (A := B.sectionPieces ⊤) s t).symm

/-- **The family is multiplicative across degrees**: the product in the Laurent algebra of the
values in degrees `i` and `j` is the value in degree `i + j` on the product of the two
homogeneous sections. -/
theorem laurentMul_sectionsMapInt [IsAffine S] (hd : 0 < d) (i j : ℤ)
    (s : Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (d : ℤ)), ⊤))
    (t : Γ(AffineTwisting.pieceMod (situationAlgebra B) (j * (d : ℤ)), ⊤)) :
    AffineTwisting.laurentMul (structureHom B ψ hgen) L i j
        (sectionsMapInt B ψ hgen i s) (sectionsMapInt B ψ hgen j t)
      = sectionsMapInt B ψ hgen (i + j)
          (AffineTwisting.algebraMul (situationAlgebra B) (d : ℤ) i j s t) := by
  match i, j with
  | .negSucc k, j =>
      obtain rfl := sections_eq_zero_of_neg B hd (Int.negSucc_lt_zero k) s
      rw [map_zero, AffineTwisting.algebraMul_zero_left, map_zero]
      exact AffineTwisting.laurentMul_zero_left _ _ _ _ _
  | .ofNat n, .negSucc k =>
      obtain rfl := sections_eq_zero_of_neg B hd (Int.negSucc_lt_zero k) t
      rw [map_zero, AffineTwisting.algebraMul_zero_right, map_zero]
      exact AffineTwisting.laurentMul_zero_right _ _ _ _ _
  | .ofNat n, .ofNat m =>
      have hmul := ψ.map_mul n m (B.ofGrading ⊤ (n * d) s) (B.ofGrading ⊤ (m * d) t)
        (B.ofGrading ⊤ ((n + m) * d)
          (AffineTwisting.algebraMul (situationAlgebra B) (d : ℤ) (n : ℤ) (m : ℤ) s t))
        (coe_ofGrading_algebraMul B n m s t)
      refine Eq.trans (Stacks.AlgebraicGeometry.CoherentMulSections.mulBilinear_mulSections L n m
        (ψ.toFun n (B.ofGrading ⊤ (n * d) s)) (ψ.toFun m (B.ofGrading ⊤ (m * d) t))) ?_
      exact congrArg ((powCompare L (n + m)).hom.app ⊤) hmul.symm

/-! ### The unit -/

/-- **The unit condition**: the family carries the unit of `𝒜^{(d)}` to the unit of the Laurent
algebra. -/
theorem sectionsMapInt_algebraOne [IsAffine S] :
    sectionsMapInt B ψ hgen 0 (AffineTwisting.algebraOne (situationAlgebra B) (d : ℤ))
      = AffineTwisting.laurentOne (structureHom B ψ hgen) L := by
  have hcomp : (powCompare L 0).hom.app ⊤ (unitGlobal L) = (1 : Γ(T, ⊤)) :=
    Stacks.AlgebraicGeometry.CoherentMulSections.powCompare_zero_globalSection_id L
  have h1 : ((B.ofGrading ⊤ (0 * d)
        (AffineTwisting.algebraOne (situationAlgebra B) (d : ℤ)) : B.grading ⊤ (0 * d)) :
      B.sectionRing ⊤) = 1 :=
    (of_eqToHom_piece B (Nat.zero_mul d).symm _ _).trans
      (DirectSum.one_def (A := B.sectionPieces ⊤)).symm
  have h2 : ψ.toFun 0 (B.ofGrading ⊤ (0 * d)
      (AffineTwisting.algebraOne (situationAlgebra B) (d : ℤ))) = unitGlobal L :=
    toFun_zero_eq_unitGlobal B ψ hgen _ h1
  exact (congrArg ((powCompare L 0).hom.app ⊤) h2).trans hcomp

/-! ### The twisting -/

/-- **The twisting `ψ : f^*𝒜^{(d)} ⟶ ⨁_{n ∈ ℤ} L^{⊗ n}` of a triple over an affine base**, the
datum `ψ` of a quadruple of Section 01NS: `Stacks.AlgebraicGeometry.AffineTwisting.ofSections`
applied to the degreewise linear maps `sectionsMapInt` of the triple, over `structureHom`. -/
def twisting [IsAffine S] (hd : 0 < d) :
    Twisting (structureHom B ψ hgen) (situationAlgebra B) (d : ℤ) L :=
  AffineTwisting.ofSections (structureHom B ψ hgen) (situationAlgebra B) (d : ℤ) L
    (fun i => B.isQuasicoherent i) (sectionsMapInt B ψ hgen)
    (laurentMul_sectionsMapInt B ψ hgen hd) (sectionsMapInt_algebraOne B ψ hgen)

/-- **The twisting realises the triple's degreewise maps on global sections**: its degree-`i`
component sends the pullback-unit image of a homogeneous section of `𝒜_{id}` over `S` to the value
of `ψ` on it, read on the integral tensor power. -/
theorem twisting_app_pullbackUnit [IsAffine S] (hd : 0 < d) (i : ℤ)
    (x : Γ(AffineTwisting.pieceMod (situationAlgebra B) (i * (d : ℤ)), ⊤)) :
    ((twisting B ψ hgen hd).app i).val.app
        ((RingedSpaceModuleAdjunction.opensMap
          (ringedSpaceHom (structureHom B ψ hgen))).op.obj (op ⊤))
        (Stacks.RingedSpace.pullbackUnit (ringedSpaceHom (structureHom B ψ hgen))
          ((situationAlgebra B).piece (i * (d : ℤ))) (op ⊤) x)
      = sectionsMapInt B ψ hgen i x :=
  AffineTwisting.ofSections_app_pullbackUnit (structureHom B ψ hgen) (situationAlgebra B) (d : ℤ) L
    (fun j => B.isQuasicoherent j) (sectionsMapInt B ψ hgen)
    (laurentMul_sectionsMapInt B ψ hgen hd) (sectionsMapInt_algebraOne B ψ hgen) i x

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTripleSections

end
