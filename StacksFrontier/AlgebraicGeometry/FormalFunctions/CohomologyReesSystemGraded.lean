module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesIdealPowerComparison

/-!
# The action of the Rees algebra of an ideal of the base on an arbitrary graded module

Let `A` be a ring, `I ⊆ A` an ideal, `X` a scheme over `Spec A` and `ℐ = I · 𝒪_X` the extension
of `I` to `X`. Every element `a ∈ Iᵏ` gives a global section of the degree-`k` piece of the Rees
algebra `⨁ₙ ℐⁿ`, so the Rees algebra `B = ⨁ₙ Iⁿ` of `I` in `A` acts on the pieces of an arbitrary
graded `⨁ₙ ℐⁿ`-module. At the graded module `⨁ₙ ℐⁿℱ` of ideal-power multiples of an
`𝒪_X`-module `ℱ` this action is multiplication by `a` from `ℐⁿℱ` to `ℐⁿ⁺ᵏℱ`.

## Main definitions

* `SheafOfModules.GradedModule.smulSectionsHom`: for a graded module `M` over a sheaf of graded
  algebras `B` on an arbitrary site, multiplication by a *global* homogeneous section of `B` of
  degree `i`, as a morphism of sheaves of modules `Mₙ ⟶ Mₙ₊ᵢ`.
* `Stacks.Cohomology.FormalFunctions.baseReesSection`: the global section of the degree-`k`
  piece of the Rees algebra of `I · 𝒪_X` attached to an element of `Iᵏ`.
* `Stacks.Cohomology.FormalFunctions.baseReesLift`: the same, as a morphism `𝒪_X ⟶ ℐᵏ`; the
  section is its value at the unit section of `𝒪_X`.
* `Stacks.Cohomology.FormalFunctions.submoduleCast`: transport along an equality of subsheaves
  of a fixed `𝒪_X`-module, as a morphism.

## Main results

* `Stacks.Cohomology.FormalFunctions.reesPieceAmbient_baseReesSection`: the image in `Γ(X, U)`
  of `baseReesSection` is the restriction of the global function attached to `a`.
* `Stacks.Cohomology.FormalFunctions.eval_baseReesSection_add`,
  `eval_baseReesSection_smul`, `eval_baseReesSection_one` and
  `reesPieceAmbient_reesMultiplication_baseReesSection`: `a ↦ baseReesSection a` is additive,
  `A`-linear, unital and multiplicative.
* `Stacks.Cohomology.FormalFunctions.smulSectionsHom_reesGradedModule_eq`: at `M = ⨁ₙ ℐⁿℱ` the
  action of `a ∈ Iᵏ` is, up to the transports identifying the two models of `ℐⁿℱ`, exactly
  `Stacks.Cohomology.FormalFunctions.idealPowerSmul`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase

universe u u' v' t' a' m'

namespace SheafOfModules.GradedModule

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t'}}
  {B : SheafOfModules.GradedAlgebra.{t', a'} R}

/-- Multiplication by a global homogeneous section of degree `i` of the algebra, as a morphism
`Mₙ ⟶ Mₙ₊ᵢ` of sheaves of modules. -/
def smulSectionsHom (M : SheafOfModules.GradedModule.{t', a', m'} B) (n i : ℤ)
    (r : (B.piece i).val.sections) : M.piece n ⟶ M.piece (n + i) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom ((M.smul n i U).flip (r.eval U))
      naturality := by
        intro U V f
        apply AddCommGrpCat.hom_ext
        ext x
        exact (congrArg (fun z ↦ M.smul n i V (Stacks.restr (M.piece n).val f x) z)
            (Stacks.restr_sections (B.piece i).val r f).symm).trans
          (M.smul_naturality n i f x (r.eval U)).symm }
    (fun U b x ↦ M.smul_smul_left n i U b x (r.eval U))⟩

/-- Multiplication by a global homogeneous section, on sections: it is the action of `M`
evaluated against the value of the section over the same object. -/
@[simp]
theorem smulSectionsHom_app (M : SheafOfModules.GradedModule.{t', a', m'} B) (n i : ℤ)
    (r : (B.piece i).val.sections) (U : Cᵒᵖ) (x : (M.piece n).val.obj U) :
    ((smulSectionsHom M n i r).val.app U) x = M.smul n i U x (r.eval U) :=
  rfl

end SheafOfModules.GradedModule

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- The global function attached to `a : A` restricts to the global function attached to
`a`. -/
theorem res_baseRingToSections {U V : X.left.Opens} (h : V ≤ U) (a : A) :
    (X.left.presheaf.map (homOfLE h).op).hom
        (baseRingToSections A X (op U) a : Γ(X.left, U)) =
      (baseRingToSections A X (op V) a : Γ(X.left, V)) := by
  change (X.left.presheaf.map (homOfLE h).op).hom
      ((X.left.presheaf.map (homOfLE (le_top (a := U))).op).hom
        (((Scheme.ΓSpecIso (.of A)).inv ≫ X.hom.appTop).hom a)) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- Over an affine open the function attached to `a ∈ Iᵏ` lies in the `k`-th power of the ideal
that `I · 𝒪_X` cuts out there. -/
theorem baseRingToSections_mem_pow (k : ℕ) {a : A} (ha : a ∈ I ^ k) (V : X.left.affineOpens) :
    (baseRingToSections A X (op V.1) a : Γ(X.left, V.1)) ∈
      ((baseIdealSheaf A I X.hom).ideal V) ^ k := by
  rw [baseIdealSheaf_ideal, ← Ideal.map_pow, ← baseIdeal_pow]
  exact Ideal.mem_map_of_mem _ (mem_baseIdeal A (I ^ k) X.hom ha)

/-- The global function attached to `a : A`, read as a section of `𝒪_X` over `U`. -/
def baseUnitSection (a : A) (U : X.left.Opens) :
    (SheafOfModules.unit X.left.ringCatSheaf).val.obj (op U) :=
  baseRingToSections A X (op U) a

/-- The function attached to `a ∈ Iᵏ` is killed by `𝒪_X ⟶ (ι_k)_* 𝒪_{V(Iᵏ𝒪_X)}`, i.e. it is a
section of the degree-`k` piece of the Rees algebra of `I · 𝒪_X`. -/
theorem quotient_baseUnitSection_eq_zero (k : ℕ) {a : A} (ha : a ∈ I ^ k) (U : X.left.Opens) :
    ((SheafOfModules.unitToPushforwardObjUnit
        (((baseIdealSheaf A I X.hom) ^ k).subschemeι.toRingCatSheafHom)).val.app (op U)).hom
      (baseUnitSection X a U) = 0 := by
  let J := (baseIdealSheaf A I X.hom) ^ k
  let q := SheafOfModules.unitToPushforwardObjUnit J.subschemeι.toRingCatSheafHom
  let Q := (SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit J.subscheme.ringCatSheaf)
  apply TopCat.Presheaf.IsSheaf.section_ext (U := op U) Q.isSheaf
  intro z hz
  obtain ⟨V, ⟨V₀, hV₀, rfl⟩, hzV, hVU⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hz U.2
  let V : X.left.affineOpens := ⟨V₀, hV₀⟩
  let h : V.1 ≤ U := hVU
  let f := (homOfLE h).op
  have hmem : (baseRingToSections A X (op V.1) a : Γ(X.left, V.1)) ∈ J.ideal V := by
    change (baseRingToSections A X (op V.1) a : Γ(X.left, V.1)) ∈
      ((baseIdealSheaf A I X.hom) ^ k).ideal V
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    exact baseRingToSections_mem_pow I X k ha V
  have hqV : ((q.val.app (op V.1)).hom) (baseUnitSection X a V.1) = 0 := by
    change (J.subschemeι.app V.1).hom
      (baseRingToSections A X (op V.1) a : Γ(X.left, V.1)) = 0
    exact RingHom.mem_ker.mp ((J.ker_subschemeι_app V).ge hmem)
  refine ⟨V.1, h, hzV, ?_⟩
  change ConcreteCategory.hom (Q.val.map f)
      (((q.val.app (op U)).hom) (baseUnitSection X a U)) =
    ConcreteCategory.hom (Q.val.map f) 0
  have hunit : ConcreteCategory.hom ((SheafOfModules.unit X.left.ringCatSheaf).val.map f)
      (baseUnitSection X a U) = baseUnitSection X a V.1 :=
    res_baseRingToSections X h a
  have hnat : ConcreteCategory.hom (Q.val.map f)
      (((q.val.app (op U)).hom) (baseUnitSection X a U)) =
      ((q.val.app (op V.1)).hom)
        (ConcreteCategory.hom ((SheafOfModules.unit X.left.ringCatSheaf).val.map f)
          (baseUnitSection X a U)) :=
    (PresheafOfModules.naturality_apply q.val f _).symm
  rw [hnat, hunit, hqV, map_zero]
  rfl

/-- `𝒪_X`, as an object of the category of `𝒪_X`-modules. -/
abbrev unitModule : X.left.Modules := SheafOfModules.unit X.left.ringCatSheaf

/-- The pushforward to `X` of the structure sheaf of the closed subscheme cut out by
`Iᵏ · 𝒪_X`. -/
abbrev baseSubschemeUnit (k : ℕ) : X.left.Modules :=
  (SheafOfModules.pushforward
      (((baseIdealSheaf A I X.hom) ^ k).subschemeι.toRingCatSheafHom)).obj
    (SheafOfModules.unit ((baseIdealSheaf A I X.hom) ^ k).subscheme.ringCatSheaf)

/-- The quotient map `𝒪_X ⟶ 𝒪_{V(Iᵏ𝒪_X)}`, whose kernel is the degree-`k` piece of the Rees
algebra of `I · 𝒪_X`. -/
abbrev baseQuotientHom (k : ℕ) : unitModule X ⟶ baseSubschemeUnit I X k :=
  SheafOfModules.unitToPushforwardObjUnit _

/-- Multiplication by `a ∈ Iᵏ` on `𝒪_X` followed by the quotient map to `𝒪_{V(Iᵏ𝒪_X)}` is
zero. -/
theorem baseSmul_comp_quotient_eq_zero (k : ℕ) {a : A} (ha : a ∈ I ^ k) :
    (a • 𝟙 (unitModule X)) ≫ baseQuotientHom I X k = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x ↦ ?_
  change (((baseIdealSheaf A I X.hom) ^ k).subschemeι.app U.unop).hom
      (Stacks.Blowup.ringSectionToGamma (baseRingToSections A X U a) *
        Stacks.Blowup.ringSectionToGamma x) = 0
  rw [map_mul]
  have h0 := quotient_baseUnitSection_eq_zero I X k ha U.unop
  change (((baseIdealSheaf A I X.hom) ^ k).subschemeι.app U.unop).hom
      (Stacks.Blowup.ringSectionToGamma (baseRingToSections A X U a)) = 0 at h0
  rw [h0, zero_mul]

/-- Multiplication by `a ∈ Iᵏ`, as a morphism from `𝒪_X` to the degree-`k` piece of the Rees
algebra of `I · 𝒪_X`. -/
def baseReesLift (k : ℕ) (a : A) (ha : a ∈ I ^ k) :
    unitModule X ⟶ Stacks.Blowup.idealPowerKernel (baseIdealSheaf A I X.hom) k :=
  kernel.lift (baseQuotientHom I X k) (a • 𝟙 (unitModule X))
    (baseSmul_comp_quotient_eq_zero I X k ha)

/-- Followed by the inclusion of the degree-`k` piece into `𝒪_X`, the lift of multiplication by
`a` is multiplication by `a`. -/
theorem baseReesLift_comp_ι (k : ℕ) (a : A) (ha : a ∈ I ^ k) :
    baseReesLift I X k a ha ≫ kernel.ι (baseQuotientHom I X k) = a • 𝟙 (unitModule X) :=
  kernel.lift_ι _ _ _

/-- The global section of the degree-`k` piece of the Rees algebra of `I · 𝒪_X` attached to
`a ∈ Iᵏ`. -/
def baseReesSection (k : ℕ) (a : A) (ha : a ∈ I ^ k) :
    (Stacks.Blowup.reesPiece (baseIdealSheaf A I X.hom) (k : ℤ)).val.sections :=
  (Stacks.Blowup.reesPiece (baseIdealSheaf A I X.hom) (k : ℤ)).val.sectionsMk
    (fun U ↦ (baseReesLift I X k a ha).val.app U (Stacks.Blowup.unitOne U.unop))
    (fun {U V} f ↦ ((PresheafOfModules.naturality_apply (baseReesLift I X k a ha).val f
        (Stacks.Blowup.unitOne U.unop)).symm.trans
      (congrArg ((baseReesLift I X k a ha).val.app V)
        (PresheafOfModules.unit_map_one (R := X.left.ringCatSheaf.obj) f))))

/-- The image in `Γ(X, U)` of the global section attached to `a ∈ Iᵏ` is the function attached
to `a`. -/
theorem reesPieceAmbient_baseReesSection (k : ℕ) (a : A) (ha : a ∈ I ^ k) (U : X.left.Opens) :
    Stacks.Blowup.reesPieceAmbient (baseIdealSheaf A I X.hom) (k : ℤ) U
        ((baseReesSection I X k a ha).eval (op U)) =
      Stacks.Blowup.ringSectionToGamma (baseRingToSections A X (op U) a) := by
  have h := congrArg (fun φ : unitModule X ⟶ unitModule X ↦
    (φ.val.app (op U)).hom (Stacks.Blowup.unitOne U)) (baseReesLift_comp_ι I X k a ha)
  change Stacks.Blowup.idealPowerKernelAmbient (baseIdealSheaf A I X.hom) k U
      ((baseReesLift I X k a ha).val.app (op U) (Stacks.Blowup.unitOne U)) = _
  refine h.trans ?_
  change Stacks.Blowup.ringSectionToGamma (baseRingToSections A X (op U) a) *
    Stacks.Blowup.ringSectionToGamma (Stacks.Blowup.unitOne U) = _
  change _ * (1 : Γ(X.left, U)) = _
  rw [mul_one]

/-- Sections of the degree-`k` piece of the Rees algebra are determined by their images in
`Γ(X, U)`. -/
private theorem eq_of_reesPieceAmbient_eq {k : ℕ} {U : X.left.Opens}
    {x y : (Stacks.Blowup.reesPiece (baseIdealSheaf A I X.hom) (k : ℤ)).val.obj (op U)}
    (h : Stacks.Blowup.reesPieceAmbient (baseIdealSheaf A I X.hom) (k : ℤ) U x =
      Stacks.Blowup.reesPieceAmbient (baseIdealSheaf A I X.hom) (k : ℤ) U y) : x = y :=
  Stacks.Blowup.reesPieceAmbient_injective (baseIdealSheaf A I X.hom) (k : ℤ)
    (Int.natCast_nonneg k) U h

/-- The global section attached to `a ∈ Iᵏ` is additive in `a`. -/
theorem eval_baseReesSection_add (k : ℕ) {a b : A} (ha : a ∈ I ^ k) (hb : b ∈ I ^ k)
    (U : X.left.Opens) :
    (baseReesSection I X k (a + b) (Ideal.add_mem _ ha hb)).eval (op U) =
      (baseReesSection I X k a ha).eval (op U) + (baseReesSection I X k b hb).eval (op U) := by
  refine eq_of_reesPieceAmbient_eq I X ?_
  rw [reesPieceAmbient_baseReesSection, Stacks.Blowup.reesPieceAmbient_add,
    reesPieceAmbient_baseReesSection, reesPieceAmbient_baseReesSection]
  exact congrArg Stacks.Blowup.ringSectionToGamma (map_add (baseRingToSections A X (op U)) a b)

/-- The global section attached to `a ∈ Iᵏ` is `A`-linear in `a`: multiplying `a` by `c ∈ A`
multiplies the section by the function attached to `c`. -/
theorem eval_baseReesSection_smul (k : ℕ) (c : A) {a : A} (ha : a ∈ I ^ k) (U : X.left.Opens) :
    (baseReesSection I X k (c * a) (Ideal.mul_mem_left _ c ha)).eval (op U) =
      baseRingToSections A X (op U) c • (baseReesSection I X k a ha).eval (op U) := by
  refine eq_of_reesPieceAmbient_eq I X ?_
  rw [reesPieceAmbient_baseReesSection, Stacks.Blowup.reesPieceAmbient_smul,
    reesPieceAmbient_baseReesSection]
  exact congrArg Stacks.Blowup.ringSectionToGamma (map_mul (baseRingToSections A X (op U)) c a)

/-- The global sections attached to elements of `Iᵏ` and `Iˡ` multiply to the one attached to
their product, read on ambient sections. -/
theorem reesPieceAmbient_reesMultiplication_baseReesSection (k l : ℕ) {a b : A} (ha : a ∈ I ^ k)
    (hb : b ∈ I ^ l) (U : X.left.Opens) :
    Stacks.Blowup.reesPieceAmbient (baseIdealSheaf A I X.hom) ((k : ℤ) + (l : ℤ)) U
        ((Stacks.Blowup.reesMultiplication (baseIdealSheaf A I X.hom) (k : ℤ) (l : ℤ)).app (op U)
          ((baseReesSection I X k a ha).eval (op U))
          ((baseReesSection I X l b hb).eval (op U))) =
      Stacks.Blowup.ringSectionToGamma (baseRingToSections A X (op U) (a * b)) := by
  rw [Stacks.Blowup.reesMultiplication_ambient, reesPieceAmbient_baseReesSection,
    reesPieceAmbient_baseReesSection]
  exact (congrArg Stacks.Blowup.ringSectionToGamma
    (map_mul (baseRingToSections A X (op U)) a b)).symm

/-- The global section attached to `1 ∈ I⁰` is the unit of the Rees algebra. -/
theorem eval_baseReesSection_one (U : X.left.Opens) :
    (baseReesSection I X 0 1 (by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top)).eval
        (op U) =
      (Stacks.Blowup.reesUnit (baseIdealSheaf A I X.hom)).eval (op U) := by
  refine eq_of_reesPieceAmbient_eq I X ?_
  rw [reesPieceAmbient_baseReesSection]
  exact (congrArg Stacks.Blowup.ringSectionToGamma
      (map_one (baseRingToSections A X (op U)))).trans
    (Stacks.Blowup.reesUnit_ambient (baseIdealSheaf A I X.hom) (op U)).symm

section Bridge

variable (F : X.left.Modules)

/-- `idealPowerSmul`, read on ambient sections of `ℱ`: it multiplies a section by the function
attached to `a`. -/
theorem idealPowerSmul_coe {k n m : ℕ} (hm : m ≤ k + n) (a : A) (ha : a ∈ I ^ k)
    (U : (Opens X.left)ᵒᵖ) (x : (idealPowerMod I X F n).val.obj U) :
    (((idealPowerSmul I X F hm a ha).val.app U) x).1 =
      baseRingToSections A X U a • (x.1 : F.val.obj U) :=
  apply_congr X (idealPowerSmul_comp_ι I X F hm a ha) U x

/-- The action of `a ∈ Iᵏ` on the graded module `⨁ₙ ℐⁿℱ`, read on ambient sections of `ℱ`: it
multiplies a section by the function attached to `a`, exactly as `idealPowerSmul` does. -/
theorem smulSectionsHom_reesGradedModule_coe (k n : ℕ) (a : A) (ha : a ∈ I ^ k)
    (U : (Opens X.left)ᵒᵖ)
    (x : ((Stacks.Blowup.reesGradedModule (baseIdealSheaf A I X.hom) F).piece (n : ℤ)).val.obj U) :
    (((SheafOfModules.GradedModule.smulSectionsHom
          (Stacks.Blowup.reesGradedModule (baseIdealSheaf A I X.hom) F) (n : ℤ) (k : ℤ)
          (baseReesSection I X k a ha)).val.app U) x).1 =
      baseRingToSections A X U a • (x.1 : F.val.obj U) := by
  have h : (((SheafOfModules.GradedModule.smulSectionsHom
          (Stacks.Blowup.reesGradedModule (baseIdealSheaf A I X.hom) F) (n : ℤ) (k : ℤ)
          (baseReesSection I X k a ha)).val.app U) x).1 =
      Stacks.Blowup.reesPieceAmbient (baseIdealSheaf A I X.hom) (k : ℤ) U.unop
        ((baseReesSection I X k a ha).eval U) • (x.1 : F.val.obj U) := rfl
  rw [h, reesPieceAmbient_baseReesSection]
  rfl


/-- The degree-`n` piece of `⨁ₙ ℐⁿℱ` is the `n`-th member of the ideal-power filtration of
`ℱ`. -/
theorem reesMultiple_natCast_eq_idealPowerSub (n : ℕ) :
    Stacks.Blowup.reesMultiple (baseIdealSheaf A I X.hom) (n : ℤ) F = idealPowerSub I X F n :=
  Stacks.Blowup.reesMultiple_eq_idealPowerMultiple (baseIdealSheaf A I X.hom) F n

/-- The degree-`(n + k)` piece of `⨁ₙ ℐⁿℱ` is the `(k + n)`-th member of the ideal-power
filtration of `ℱ`. -/
theorem reesMultiple_add_eq_idealPowerSub (k n : ℕ) :
    Stacks.Blowup.reesMultiple (baseIdealSheaf A I X.hom) ((n : ℤ) + (k : ℤ)) F =
      idealPowerSub I X F (k + n) := by
  have hd : ((n : ℤ) + (k : ℤ)) = ((k + n : ℕ) : ℤ) := by push_cast; ring
  rw [hd]
  exact Stacks.Blowup.reesMultiple_eq_idealPowerMultiple (baseIdealSheaf A I X.hom) F (k + n)

/-- Transport along an equality of subsheaves of `F`, as a morphism of `𝒪_X`-modules. -/
def submoduleCast {P Q : F.Submodule} (e : P = Q) :
    (P.toSheafOfModules : X.left.Modules) ⟶ (Q.toSheafOfModules : X.left.Modules) :=
  eqToHom (congrArg (fun N : F.Submodule ↦ (N.toSheafOfModules : X.left.Modules)) e)

/-- Transport along an equality of subsheaves is compatible with the inclusions into `ℱ`. -/
@[simp]
theorem submoduleCast_comp_ι {P Q : F.Submodule} (e : P = Q) :
    submoduleCast X F e ≫ Q.ι = P.ι := by
  subst e
  exact Category.id_comp _

/-- Transport along an equality of subsheaves does not change an ambient section of `ℱ`. -/
@[simp]
theorem submoduleCast_coe {P Q : F.Submodule} (e : P = Q) (U : (Opens X.left)ᵒᵖ)
    (y : (P.toSheafOfModules).val.obj U) :
    (((submoduleCast X F e).val.app U) y).1 = (y.1 : F.val.obj U) := by
  subst e
  rfl

/-- At `M = ⨁ₙ ℐⁿℱ` the action of `a ∈ Iᵏ` on an arbitrary graded module is `idealPowerSmul`,
up to the identification of the two models of `ℐⁿℱ` and the degree bookkeeping
`n + k = k + n`. -/
theorem smulSectionsHom_reesGradedModule_eq (k n : ℕ) (a : A) (ha : a ∈ I ^ k) :
    SheafOfModules.GradedModule.smulSectionsHom
        (Stacks.Blowup.reesGradedModule (baseIdealSheaf A I X.hom) F) (n : ℤ) (k : ℤ)
        (baseReesSection I X k a ha) =
      submoduleCast X F (reesMultiple_natCast_eq_idealPowerSub I X F n) ≫
        idealPowerSmul I X F (le_refl (k + n)) a ha ≫
          submoduleCast X F (reesMultiple_add_eq_idealPowerSub I X F k n).symm := by
  refine cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦ ?_)
  refine (smulSectionsHom_reesGradedModule_coe I X F k n a ha U x).trans ?_
  change _ = ((((submoduleCast X F (reesMultiple_add_eq_idealPowerSub I X F k n).symm).val.app U)
      (((idealPowerSmul I X F (le_refl (k + n)) a ha).val.app U)
        (((submoduleCast X F (reesMultiple_natCast_eq_idealPowerSub I X F n)).val.app U) x)))).1
  rw [submoduleCast_coe, idealPowerSmul_coe]
  exact congrArg (fun z : F.val.obj U ↦ baseRingToSections A X U a • z)
    (submoduleCast_coe X F (reesMultiple_natCast_eq_idealPowerSub I X F n) U x).symm

end Bridge

end Stacks.Cohomology.FormalFunctions

end
