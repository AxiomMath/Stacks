module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionTower
public import StacksCore.Tactic.StacksAttribute

/-!
# The good surjection onto a differential graded module

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it and
let `M` be a right differential graded `A`-module. This file produces a homomorphism `P ⟶ M`
which is surjective, which is surjective on the sections killed by the differentials, and whose
source is flat as a graded module and K-flat.

The module `P` is the first stage of the tower of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionTower.lean`: the
twisted extension of the free differential graded module `A[Z(M)]` on the sheaf of graded sets of
closed sections of `M` by the free module on the sheaf of graded sets of boundary pairs of
`τ₀ : A[Z(M)] ⟶ M`, with the homomorphism to `M` of
`SheafOfModules.DifferentialGradedModule.towerStepMap`. Nothing is an argument but `M`.

## Main results

* `SheafOfModules.exists_pullback_section`: a compatible pair of local sections of two sheaves of
  modules over a common target is a local section of their fibre product.
* `SheafOfModules.DifferentialGradedModule.exists_boundaryPair_primitive`: every local section of
  `M^n` is the second component of a boundary pair of `τ₀` of degree `n + 1`.
* `SheafOfModules.DifferentialGradedModule.epi_f_towerStepMap`: **clause (1)**, the homomorphism
  from the first stage is an epimorphism of sheaves of modules in every degree.
* `SheafOfModules.DifferentialGradedModule.exists_closed_preimage_towerStepMap`: **clause (2)**,
  every local section of `M^n` killed by the differential is the image of a local section of the
  first stage killed by the differential, and
  `SheafOfModules.DifferentialGradedModule.epi_cyclesMap_towerStepMap`, the same clause read as
  an epimorphism on the sheaves of cocycles.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_towerStepFreeOnClosedSections` and
  `SheafOfModules.DifferentialGradedModule.isKFlat_towerStepFreeOnClosedSections`: **clause
  (3)**, conditions (1) and (2) of the definition of good in Section 0FSA.
* `SheafOfModules.DifferentialGradedModule.exists_flat_surjection` bundles the three clauses,
  with `M` as its only argument.

## Implementation notes

**Clause (1).** Over an object `V` of the site let `x` be a local section of `M^n`. Its
differential is a cocycle of `M` of degree `n + 1`, so by
`SheafOfModules.exists_closed_preimage_freeOnClosedSectionsHom` it is the image of a local
section of `A[Z(M)]^{n+1}` killed by the differential, hence by
`SheafOfModules.exists_cycles_section` of a local section of the cocycle sheaf. That local
section and `x` are compatible over the cocycle sheaf of `M` of degree `n + 1`, so by
`SheafOfModules.exists_pullback_section` they are the two components of a boundary pair of
degree `n + 1`. The generator that pair names is carried by the homotopy
`SheafOfModules.DifferentialGradedModule.stepHomotopy` to the second component of the pair,
which is `x`, and the degree-`n` component of
`SheafOfModules.DifferentialGradedModule.towerStepMap` restricts to that homotopy along the
first coordinate of the degreewise splitting of the cone
(`SheafOfModules.DifferentialGradedModule.towerStepFreeInclusion`). So `x` is the image of a
local section, and `SheafOfModules.DifferentialGradedModule.epi_of_surjective_sections`
concludes.

**Clause (2).** A local section of `M^n` killed by the differential is the image of a local
section of `A[Z(M)]^n` killed by the differential, and the inclusion of `A[Z(M)]` into the first
stage is a morphism of complexes which does not change the image in `M`, by
`SheafOfModules.DifferentialGradedModule.twistedExtensionInclusion_towerStepMap`. Since kernels
of sheaves of modules are computed sectionwise, surjectivity on the sections killed by the
differential is stronger than surjectivity of `Ker(d_P) ⟶ Ker(d_M)`; the epimorphism of cocycle
sheaves is `SheafOfModules.epi_cyclesMap_of_exists_closed_preimage`.

**Clause (3).** Flatness of the underlying graded module and K-flatness propagate along the
twisted extension by `SheafOfModules.DifferentialGradedModule.twistedExtension_isGradedFlat` and
`SheafOfModules.DifferentialGradedModule.twistedExtension_isKFlat`, from the flatness and
K-flatness of a free differential graded module (Tag 0FSG). Condition (3) of the definition of
good in Section 0FSA, stability under arbitrary base change, holds for this same module too and
is concluded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionToposQuotient.lean`
by `SheafOfModules.DifferentialGradedModule.exists_good_surjection`, which delivers the whole of
`SheafOfModules.IsGoodToposBaseChange`. That reading asks for a ringed topos and identifies the
ring universe with the module universe, which is why it lives there and this file keeps the two
universes independent.

**The section of a fibre product.** The functor `SheafOfModules.forget R` followed by evaluation
at an object of the site preserves finite limits, so it carries the fibre product square to a
fibre product square of modules, and the elements of a fibre product of modules are the
compatible pairs — `CategoryTheory.Limits.Concrete.pullbackMk`, transported along the comparison
of the two limit cones. This mirrors `SheafOfModules.exists_cycles_section`, which does the same
for a kernel.

**Degrees.** A boundary pair of degree `n + 1` has its second component in `M^{(n+1)-1}`, which
is only propositionally the same sheaf as `M^n`, so the two are related by
`SheafOfModules.castHom` as everywhere in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`. The equalities of degrees
are written as term proofs, `add_sub_cancel_right` and its symmetric form.

## References

* [Stacks Project, Tag 0FSE](https://stacks.math.columbia.edu/tag/0FSE)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

/-! ### Transport of local sections along an equality of degrees -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transporting a local section along an equality of degrees and back again changes nothing. -/
theorem castHom_castHom_symm (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (h' : j = i)
    (U : Cᵒᵖ) (z : (X i).val.obj U) : castHom X h' U (castHom X h U z) = z := by
  subst h
  rfl

/-- The differential of a cochain complex of sheaves of modules, read on a local section
transported into a propositionally equal source degree. -/
theorem homSections_d_castHom (N : CochainComplex (SheafOfModules.{m} R) ℤ) {p p' : ℤ}
    (h : p = p') (q : ℤ) (U : Cᵒᵖ) (z : (N.X p).val.obj U) :
    homSections (N.d p' q) U (castHom N.X h U z) = homSections (N.d p q) U z := by
  subst h
  rfl

/-- A composite of morphisms of sheaves of modules, read on sections, is the map of any equal
morphism. -/
private theorem homSections_homSections_of_comp_eq {X Y Z : SheafOfModules.{m} R}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (e : f ≫ g = h) (V : Cᵒᵖ) (z : X.val.obj V) :
    homSections g V (homSections f V z) = homSections h V z :=
  (homSections_comp f g V z).symm.trans (homSections_congr e V z)

end Transport

/-! ### Local sections of a fibre product -/

section Pullback

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] in
/-- **A compatible pair of local sections is a local section of the fibre product.** Taking
sections over an object of the site is left exact, so it carries the fibre product square to a
fibre product square of modules, whose elements are the compatible pairs. -/
theorem exists_pullback_section {X Y Z : SheafOfModules.{m} R}
    (f : X ⟶ Z) (g : Y ⟶ Z) (V : Cᵒᵖ) (x : X.val.obj V) (y : Y.val.obj V)
    (h : homSections f V x = homSections g V y) :
    ∃ w : (Limits.pullback f g).val.obj V,
      homSections (Limits.pullback.fst f g) V w = x ∧
        homSections (Limits.pullback.snd f g) V w = y := by
  let E := SheafOfModules.forget.{m} R ⋙ PresheafOfModules.evaluation R.obj V
  have hpl : PreservesLimit (cospan f g) E :=
    PreservesFiniteLimits.preservesFiniteLimits _ |>.preservesLimit
  have hlim := isLimitOfHasPullbackOfPreservesLimit E f g
  let iso := IsLimit.conePointUniqueUpToIso (pullbackIsPullback (E.map f) (E.map g)) hlim
  have h' : (E.map f) x = (E.map g) y := h
  let p := Concrete.pullbackMk (E.map f) (E.map g) x y h'
  have hfst : iso.hom ≫ E.map (Limits.pullback.fst f g)
      = Limits.pullback.fst (E.map f) (E.map g) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ hlim WalkingCospan.left
  have hsnd : iso.hom ≫ E.map (Limits.pullback.snd f g)
      = Limits.pullback.snd (E.map f) (E.map g) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ hlim WalkingCospan.right
  refine ⟨iso.hom p, ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom hfst p).trans
      (Concrete.pullbackMk_fst (E.map f) (E.map g) x y h')
  · exact (ConcreteCategory.congr_hom hsnd p).trans
      (Concrete.pullbackMk_snd (E.map f) (E.map g) x y h')

end Pullback

namespace DifferentialGradedModule

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-! ### The free module on the boundary pairs inside the next stage -/

/-- **The first coordinate of the degreewise splitting of the next stage of the tower**: the
degree-`n` piece of the twisted extension of `P` by the free module on the boundary pairs of
`τ : P ⟶ M` is `A[S]^{n+1} ⊞ P^n`, and this is the inclusion of the first summand. -/
noncomputable def towerStepFreeInclusion {M P : DifferentialGradedModule.{t, m, m} A}
    (τ : P ⟶ M) (n : ℤ) :
    (freeDGModule (boundaryPairs τ.toHomologicalComplex) A).complex.X (n + 1) ⟶
      (towerStep τ).complex.X n :=
  biprod.inl ≫ ((conePackage (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P
    (boundaryPairFamily τ) (boundaryPairFamily_closed τ))).componentIso n).inv

/-- **On the free module on the boundary pairs, the map to `M` is the homotopy.** The map out of
the cone is the splitting followed by its two coordinates, and the first of them is
`SheafOfModules.DifferentialGradedModule.stepHomotopy`. -/
theorem towerStepFreeInclusion_towerStepMap {M P : DifferentialGradedModule.{t, m, m} A}
    (τ : P ⟶ M) (n : ℤ) :
    towerStepFreeInclusion τ n ≫ (towerStepMap τ).toHomologicalComplex.f n
      = stepHomotopy τ n := by
  have hdf : (towerStepMap τ).toHomologicalComplex.f n
      = ((conePackage (dgLiftHom (boundaryPairs τ.toHomologicalComplex) A P (boundaryPairFamily τ)
            (boundaryPairFamily_closed τ))).componentIso n).hom ≫
          biprod.desc (stepHomotopy τ n) (τ.toHomologicalComplex.f n) :=
    ConePackage.desc_f _ τ (stepHomotopy τ) (stepHomotopy_mul τ) (stepHomotopy_delta τ) n
  rw [towerStepFreeInclusion, hdf, Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_desc]

/-- **The map to `M` from the next stage of the tower hits the second component of every boundary
pair**, on the local section named by the generator that pair carries. -/
theorem homSections_towerStepMap_generator {M P : DifferentialGradedModule.{t, m, m} A}
    (τ : P ⟶ M) (n : ℤ) (V : Cᵒᵖ) (y : (boundaryPairObj τ.toHomologicalComplex (n + 1)).val.obj V) :
    homSections ((towerStepMap τ).toHomologicalComplex.f n) V
        (homSections (towerStepFreeInclusion τ n) V
          (freeGeneratorSection A.toGradedAlgebra (boundaryPairs τ.toHomologicalComplex) (n + 1) V
            (boundaryPairSection τ.toHomologicalComplex (n + 1) V y)
            (boundaryPairSection_hasDegree τ.toHomologicalComplex (n + 1) V y)))
      = castHom M.complex.X (add_sub_cancel_right n 1) V
          (homSections (boundaryPairPrimitive τ.toHomologicalComplex (n + 1)) V y) :=
  (homSections_homSections_of_comp_eq (towerStepFreeInclusion_towerStepMap τ n) V _).trans
    (stepHomotopy_generator τ n V y)

/-! ### Every local section of `M` is the second component of a boundary pair -/

/-- **Every local section of `M^n` is the second component of a boundary pair of
`τ₀ : A[Z(M)] ⟶ M` of degree `n + 1`.** Its differential is a cocycle of `M` of degree `n + 1`,
hence the image of a local section of the cocycle sheaf of `A[Z(M)]`; that local section and the
given one are compatible over the cocycle sheaf of `M`, so they are the two components of a
boundary pair. -/
theorem exists_boundaryPair_primitive (M : DifferentialGradedModule.{t, m, m} A) (n : ℤ)
    (V : Cᵒᵖ) (x : (M.complex.X n).val.obj V) :
    ∃ y : (boundaryPairObj (freeOnClosedSectionsHom M).toHomologicalComplex (n + 1)).val.obj V,
      castHom M.complex.X (add_sub_cancel_right n 1) V
          (homSections (boundaryPairPrimitive (freeOnClosedSectionsHom M).toHomologicalComplex
            (n + 1)) V y) = x := by
  have hdd : homSections (M.complex.d (n + 1) ((n + 1) + 1)) V
      (homSections (M.complex.d n (n + 1)) V x) = 0 :=
    (homSections_congr (M.complex.d_comp_d n (n + 1) ((n + 1) + 1)) V x).trans
      (homSections_zero V x)
  obtain ⟨y₀, hdy₀, hy₀⟩ := exists_closed_preimage_freeOnClosedSectionsHom M (n + 1) V
    (homSections (M.complex.d n (n + 1)) V x) hdd
  obtain ⟨ξ, hξ⟩ := exists_cycles_section
    (freeDGModule (closedSections M.complex) A).complex (n + 1) V y₀ hdy₀
  have hcond : homSections (HomologicalComplex.cyclesMap
        (freeOnClosedSectionsHom M).toHomologicalComplex (n + 1)) V ξ =
      homSections (M.complex.toCycles ((n + 1) - 1) (n + 1)) V
        (castHom M.complex.X (add_sub_cancel_right n 1).symm V x) := by
    refine injective_iCycles_sections M.complex (n + 1) V ?_
    calc homSections (M.complex.iCycles (n + 1)) V
          (homSections (HomologicalComplex.cyclesMap
            (freeOnClosedSectionsHom M).toHomologicalComplex (n + 1)) V ξ)
        = homSections ((freeDGModule (closedSections M.complex) A).complex.iCycles (n + 1) ≫
            (freeOnClosedSectionsHom M).toHomologicalComplex.f (n + 1)) V ξ :=
          homSections_homSections_of_comp_eq (HomologicalComplex.cyclesMap_i _ (n + 1)) V ξ
      _ = homSections ((freeOnClosedSectionsHom M).toHomologicalComplex.f (n + 1)) V y₀ :=
          congrArg (fun z =>
            homSections ((freeOnClosedSectionsHom M).toHomologicalComplex.f (n + 1)) V z) hξ
      _ = homSections (M.complex.d n (n + 1)) V x := hy₀
      _ = homSections (M.complex.d ((n + 1) - 1) (n + 1)) V
            (castHom M.complex.X (add_sub_cancel_right n 1).symm V x) :=
          (homSections_d_castHom M.complex (add_sub_cancel_right n 1).symm (n + 1) V x).symm
      _ = homSections (M.complex.iCycles (n + 1)) V
            (homSections (M.complex.toCycles ((n + 1) - 1) (n + 1)) V
              (castHom M.complex.X (add_sub_cancel_right n 1).symm V x)) :=
          (homSections_homSections_of_comp_eq (M.complex.toCycles_i ((n + 1) - 1) (n + 1)) V _).symm
  obtain ⟨w, -, hw⟩ := exists_pullback_section
    (HomologicalComplex.cyclesMap (freeOnClosedSectionsHom M).toHomologicalComplex (n + 1))
    (M.complex.toCycles ((n + 1) - 1) (n + 1)) V ξ
    (castHom M.complex.X (add_sub_cancel_right n 1).symm V x) hcond
  exact ⟨w, (congrArg (fun z => castHom M.complex.X (add_sub_cancel_right n 1) V z) hw).trans
    (castHom_castHom_symm M.complex.X (add_sub_cancel_right n 1).symm
      (add_sub_cancel_right n 1) V x)⟩

/-! ### Clause (1): surjectivity -/

/-- **Clause (1) of Tag 0FSE.** The homomorphism to `M` from the first stage of the tower is
surjective: its degree-`n` component is an epimorphism of sheaves of modules, for every `n`.
Every local section of `M^n` is the second component of a boundary pair of degree `n + 1`, and
the generator that pair names is carried to it. -/
theorem epi_f_towerStepMap (M : DifferentialGradedModule.{t, m, m} A) (n : ℤ) :
    Epi ((towerStepMap (freeOnClosedSectionsHom M)).toHomologicalComplex.f n) := by
  refine epi_of_surjective_sections _ fun V x => ?_
  obtain ⟨y, hy⟩ := exists_boundaryPair_primitive M n V x
  exact ⟨_, (homSections_towerStepMap_generator (freeOnClosedSectionsHom M) n V y).trans hy⟩

/-! ### Clause (2): surjectivity on the sections killed by the differentials -/

/-- **Clause (2) of Tag 0FSE.** Every local section of `M^n` killed by the differential is the
image of a local section of the first stage of the tower killed by the differential: it is
already the image of such a local section of `A[Z(M)]^n`, and the inclusion of `A[Z(M)]` into
the first stage is a morphism of complexes which does not change the image in `M`. Since kernels
of sheaves of modules are computed sectionwise, this says in particular that
`Ker(d_P) ⟶ Ker(d_M)` is surjective. -/
theorem exists_closed_preimage_towerStepMap (M : DifferentialGradedModule.{t, m, m} A) (n : ℤ)
    (V : Cᵒᵖ) (x : (M.complex.X n).val.obj V)
    (hx : homSections (M.complex.d n (n + 1)) V x = 0) :
    ∃ z : ((towerStep (freeOnClosedSectionsHom M)).complex.X n).val.obj V,
      homSections ((towerStep (freeOnClosedSectionsHom M)).complex.d n (n + 1)) V z = 0 ∧
        homSections ((towerStepMap (freeOnClosedSectionsHom M)).toHomologicalComplex.f n) V z
          = x := by
  obtain ⟨y₀, hdy₀, hy₀⟩ := exists_closed_preimage_freeOnClosedSectionsHom M n V x hx
  refine ⟨homSections
    ((towerStepInclusion (freeOnClosedSectionsHom M)).toHomologicalComplex.f n) V y₀, ?_, ?_⟩
  · exact (homSections_homSections_of_comp_eq
      ((towerStepInclusion (freeOnClosedSectionsHom M)).toHomologicalComplex.comm n (n + 1))
      V y₀).trans (by rw [homSections_comp, hdy₀, map_zero])
  · exact (homSections_homSections_of_comp_eq (congrArg
      (fun φ : freeDGModule (closedSections M.complex) A ⟶ M => φ.toHomologicalComplex.f n)
      (twistedExtensionInclusion_towerStepMap (freeOnClosedSectionsHom M))) V y₀).trans hy₀

/-- **Clause (2) of Tag 0FSE, as an epimorphism of cocycle sheaves.** Cocycle sheaves are
computed sectionwise, taking sections over an object of the site being left exact, so this is the
previous statement. -/
theorem epi_cyclesMap_towerStepMap (M : DifferentialGradedModule.{t, m, m} A) (n : ℤ) :
    Epi (HomologicalComplex.cyclesMap
      (towerStepMap (freeOnClosedSectionsHom M)).toHomologicalComplex n) :=
  epi_cyclesMap_of_exists_closed_preimage _ n fun V x hx =>
    exists_closed_preimage_towerStepMap M n V x hx

/-! ### Clause (3): flatness of the first stage -/

/-- **The first stage of the tower is flat as a graded module**, which is condition (1) of the
definition of good in Section 0FSA: it is the twisted extension of a free differential graded
module, and both the free module and its shift are flat by Tag 0FSG. -/
theorem isGradedFlat_towerStepFreeOnClosedSections (M : DifferentialGradedModule.{t, m, m} A) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded
      (towerStep (freeOnClosedSectionsHom M))) :=
  twistedExtension_isGradedFlat (boundaryPairs (freeOnClosedSectionsHom M).toHomologicalComplex)
    (freeDGModule (closedSections M.complex) A) (boundaryPairFamily (freeOnClosedSectionsHom M))
    (boundaryPairFamily_closed (freeOnClosedSectionsHom M))
    (freeDGModule_isGradedFlat A (closedSections M.complex))

/-- **The first stage of the tower is K-flat**, which is condition (2) of the definition of good
in Section 0FSA: it is the twisted extension of a free differential graded module, and both the
free module and its shift are K-flat by Tag 0FSG. -/
theorem isKFlat_towerStepFreeOnClosedSections (M : DifferentialGradedModule.{t, m, m} A) :
    RelativeTensor.IsKFlat (towerStep (freeOnClosedSectionsHom M)) :=
  twistedExtension_isKFlat (boundaryPairs (freeOnClosedSectionsHom M).toHomologicalComplex)
    (freeDGModule (closedSections M.complex) A) (boundaryPairFamily (freeOnClosedSectionsHom M))
    (boundaryPairFamily_closed (freeOnClosedSectionsHom M))
    (freeDGModule_isKFlat (closedSections M.complex) A)

/-! ### The three clauses together -/

/-- **Tag 0FSE.** Every right differential graded `A`-module `M` receives a homomorphism from a
right differential graded `A`-module which is surjective, which is surjective on the sheaves of
cocycles, and whose source is flat as a graded module and K-flat.

The source is the first stage of the tower of the first proof of Tag 0FSH: the twisted extension
of the free differential graded module on the sheaf of graded sets of closed sections of `M` by
the free module on the sheaf of graded sets of boundary pairs of its homomorphism to `M`. It is
built from `M` alone.

Clause (2) is available on sections as well, as
`SheafOfModules.DifferentialGradedModule.exists_closed_preimage_towerStepMap`: every local
section of `M^n` killed by the differential is the image of a local section of the source killed
by the differential. Clause (3) is read here as conditions (1) and (2) of the definition of good
in Section 0FSA, flatness of the underlying graded module and K-flatness, over a ringed site and
with the ring universe and the module universe independent;
`SheafOfModules.DifferentialGradedModule.exists_good_surjection` concludes the same three clauses
for the same module with the third at the whole of goodness, over a ringed topos. -/
@[stacks 0FSE "the resolution is built from M alone: the first stage of the tower of Tag 0FSH, \
the twisted extension of the free module on the closed sections of M by the free module on the \
boundary pairs of its homomorphism to M. Clause (2) is concluded as surjectivity on the sections \
killed by the differential, which is stronger than surjectivity of Ker(d_P) to Ker(d_M), and \
also as an epimorphism on the sheaves of cocycles. Clause (3) is concluded here as conditions \
(1) and (2) of the definition of good in Section 0FSA, flatness of the underlying graded module \
and K-flatness, over a ringed site and with the ring universe and the module universe \
independent, and the whole of condition (3) for this same module is concluded over a ringed \
topos by exists_good_surjection"]
theorem exists_flat_surjection (M : DifferentialGradedModule.{t, m, m} A) :
    ∃ (Q : DifferentialGradedModule.{t, m, m} A) (π : Q ⟶ M),
      (∀ n : ℤ, Epi (π.toHomologicalComplex.f n)) ∧
        (∀ n : ℤ, Epi (HomologicalComplex.cyclesMap π.toHomologicalComplex n)) ∧
          RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded Q) ∧
            RelativeTensor.IsKFlat Q :=
  ⟨towerStep (freeOnClosedSectionsHom M), towerStepMap (freeOnClosedSectionsHom M),
    epi_f_towerStepMap M, epi_cyclesMap_towerStepMap M,
    isGradedFlat_towerStepFreeOnClosedSections M, isKFlat_towerStepFreeOnClosedSections M⟩

end DifferentialGradedModule

end SheafOfModules

end
