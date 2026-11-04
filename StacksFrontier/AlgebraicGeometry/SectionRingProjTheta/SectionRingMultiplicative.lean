module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.PowerCompareAgreement
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProj.DataIso

/-!
# The two section rings of an invertible sheaf of modules are isomorphic as graded rings

`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingComparison.lean` compares the
repository's two realisations of Stacks Tag 01CV's graded ring `Γ_*(X, L)` as graded *additive*
groups, pinned at the two spellings its consumers use:

* `Stacks.GradedSections.sectionRing L = ⨁_{n ≥ 0} (𝟙_ C ⟶ L^{⊗ n})`, which
  `Stacks.AmpleFiniteAvoidance.grading` grades and
  `Stacks.SectionRingProjMorphism.projHomOfIsAmple` takes `Proj` of;
* `Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L = ⨁_{n ≥ 0} Γ(L^{⊗ n}, ⊤_C)`, the ring the graded
  localizations of Stacks Tags 0B5L and 01PW are formed over.

This file identifies the two **products**, and so upgrades that comparison to an isomorphism of
graded rings. A graded localization cannot be transported along an additive isomorphism, so this
is what every consumer on the `Proj` side needs.

## Main definitions

* `Stacks.SectionRingProjTheta.sectionRingEquiv`: **the comparison of the two section rings as a
  `RingEquiv`.**
* `Stacks.SectionRingProjTheta.schemeSectionRingEquiv` and
  `Stacks.SectionRingProjTheta.sectionSiteSectionRingEquiv`: the same for an invertible
  `𝒪_X`-module on a scheme, the second with the structure sheaf spelled as
  `Stacks.SheafOfModules.sectionSiteRing`, which is how Tag 01PW spells it.
* `Stacks.SectionRingProjTheta.sectionGradedRingHom` and
  `Stacks.SectionRingProjTheta.sectionGradedRingHomInv`: the comparison and its inverse as
  homomorphisms of *graded* rings, from the family `Proj` is taken of to the family Tag 01PW's
  localizations are formed at and back.
* `Stacks.SectionRingProjTheta.projIso`: **`Proj` of Tag 01PW's graded ring is `Proj Γ_*(X, L)`**,
  the scheme `Stacks.SectionRingProjMorphism.projHomOfIsAmple` maps into.

## Main results

* `Stacks.SectionRingProjTheta.powSectionsAddEquiv_mul`: **multiplicativity in a single pair of
  degrees** — the degreewise carrier comparison carries `Stacks.GradedSections.mul` to
  `Stacks.SheafOfModules.sectionRingMul`. This is the one statement with content; everything else
  is the direct-sum bookkeeping on top of it.
* `Stacks.SectionRingProjTheta.sectionRingHom_mul`: the comparison of
  `SectionRingComparison.lean` is multiplicative.
* `Stacks.SectionRingProjTheta.sectionGradedRingHomInv_comp` and
  `Stacks.SectionRingProjTheta.sectionGradedRingHom_comp`: the two graded homomorphisms are
  mutually inverse, so the two graded rings are isomorphic *as graded rings* and not merely
  isomorphic through a map that happens to preserve degrees.

## Implementation notes

**The one mathematical input is already available, in a different spelling of the comparison.**
`Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare` proves multiplicativity for
`Stacks.SheafOfModules.Invertible.tensorPowerCompare`, the comparison of the two power *systems*;
`Stacks.SectionRingProjTheta.powIso`, which the carrier comparison is assembled from, is built
from the unrelated recursion `Stacks.PowerFamilyBridge.natIso`.
`Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare` identifies the two, and
`powSectionsAddEquiv_apply` is the observation that the degreewise carrier comparison is then
literally `Stacks.SheafOfModules.Invertible.tensorPowerCompareSection` evaluated at the unit
section — both sides being the morphism precomposed with
`AlgebraicGeometry.SheafOfModules.unitIso` and read at `1`, so the identification is by `rfl`
once `powIso` has been rewritten.

**The two spellings of the homogeneous product differ by a reindexing that is a transport along a
definitional equality.** `Stacks.SheafOfModules.sectionRingMul` lands in degree `((n + m : ℕ) : ℤ)`
and `Stacks.SheafOfModules.TensorPower.mulBilinear` in degree `(n : ℤ) + (m : ℤ)`, so the former
carries one extra `Stacks.SheafOfModules.TensorPower.tensorPowerReindex`.
`Stacks.SheafOfModules.TensorPower.heq_reindex` discharges it; no other difference between the two
survives, the pairing `Stacks.SheafOfModules.tensorGlobalSection` of two global sections being
`Stacks.SheafOfModules.tensorSectionsAt` over the terminal object by definition.

**Why `Eq.trans` and not one `rw` chain in `powSectionsAddEquiv_mul`.** Rewriting the three
occurrences of the carrier comparison first and the product second leaves a goal that is not
type-correct at the transparency `rw` checks its motive at: the unit section is written
`(1 : (structureSheaf 𝒪 h𝒪).obj.obj (op (⊤_ C)))` while the domain of
`tensorPowerCompareSection` is `SheafOfModules.unit (structureSheaf 𝒪 h𝒪)`, and the two agree only
up to unfolding. Discharging the product first, with `Eq.trans` against a fully elaborated
instance, keeps every later rewrite inside one spelling.

**The scheme-level statements reinstate four instances by hand, and have to.** At the
`AlgebraicGeometry.Scheme.Modules` spelling instance search supplies neither
`Stacks.SectionRingGeometric.schemeTensorRightAdditive`'s additivity nor the invertibility
`Stacks.SheafOfModules.sectionRingGradedRing` needs, because `AlgebraicGeometry.Scheme.Modules` is
not unfolded at instance transparency — the accommodation
`Stacks.SheafOfModules.sectionSiteRing`'s own file makes for the same reason, with its own
`local instance`s for `DirectSum.GCommRing` and `GradedRing`. Without `schemeTensorRightEquiv` and
`schemeSectionGCommRing` the right-hand section ring carries no multiplication at this spelling at
all, so there is nothing for the `RingEquiv` to land in.

**`(tensorRight L).Additive` has to be put back in force.** It is the hypothesis
`Stacks.GradedSections.instGRing` — hence the whole ring structure on the left-hand side — is
stated under, and `Stacks.SectionRingGeometric.tensorRightAdditive` is a `local instance` in its
own file, so this file reinstates it. `SectionRingComparison.lean` does not, because the additive
comparison does not need it.

**`projIso` repeats a construction the relative theory already carries.**
`Stacks.RelativeProj.Data.Iso.projIso` builds the same isomorphism from the same three Mathlib
lemmas, but for the graded ring a relative-`Proj` gluing datum attaches to an affine open of a
base, so it cannot be instantiated at a bare pair of graded rings. The general statement — two
mutually inverse `GradedRingHom`s induce `Proj ℬ ≅ Proj 𝒜` — is not in the library in either
place; `Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id`, which is the only part with any
content, is reused here rather than restated.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)

## What is not done here

**Nothing here transports Tag 01PW part (2) itself.** `Stacks.SectionRingProjTheta.projIso`
identifies the two `Proj`s, which is what makes a statement of Tag 01PW part (2) over
`Proj Γ_*(X, L)` expressible at all; the bijectivity
`Stacks.SheafOfModules.sectionLocalizationMap_bijective` is not restated there, and the chart
`D₊(s)` of `Proj Γ_*(X, L)` is not identified with `X_s`.

**Nothing here is Tag 0B5I's comparison family, and nothing here discharges Tag 01QJ's binder.**
Tag 0B5I is a statement about `Proj` of an *arbitrary* graded ring — a morphism
`(⨁_n Γ(Proj 𝒮, F(n)))~ ⟶ F` for every quasi-coherent `F`, natural, normalised in degree zero —
and no sheaf of modules on a `Proj` is constructed below.

**The degree-zero unit is not identified separately.** `RingEquiv` derives `map_one` from
`map_mul` and bijectivity, so no computation of the image of
`Stacks.GradedSections.gOne_def`'s unit section against
`Stacks.SheafOfModules.sectionRingGradedOne_eq`'s is carried out here; the ingredient for one, if
a consumer wants it in that shape, is
`Stacks.SheafOfModules.Invertible.tensorPowerCompareSection_id_app`.

-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Limits Opposite
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SectionRingProjTheta

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasTerminal C]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory Stacks.SectionRingGeometric.tensorRightAdditive

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-! ### Multiplicativity in a single pair of degrees -/

/-- **The degreewise carrier comparison is `tensorPowerCompareSection` at the unit section.**
`Stacks.SectionRingProjTheta.powSectionsAddEquiv` post-composes with
`Stacks.SectionRingProjTheta.powIso` and then reads the result as an honest global section, which
is precomposition with `AlgebraicGeometry.SheafOfModules.unitIso` followed by evaluation at `1`;
`Stacks.SheafOfModules.Invertible.tensorPowerCompareSection` is the same composite written with
`Stacks.SheafOfModules.Invertible.tensorPowerCompare` in place of `powIso`. The two powers
comparisons agree by `powIso_eq_tensorPowerCompare`, and nothing else has to be said. -/
theorem powSectionsAddEquiv_apply (n : ℕ) (s : Stacks.GradedSections.powSections L n) :
    powSectionsAddEquiv 𝒪 h𝒪 L n s
      = (Stacks.SheafOfModules.Invertible.tensorPowerCompareSection 𝒪 h𝒪 L s).val.app
          (op (⊤_ C)) (1 : (structureSheaf 𝒪 h𝒪).obj.obj (op (⊤_ C))) := by
  rw [Stacks.SheafOfModules.Invertible.tensorPowerCompareSection,
    ← powIso_eq_tensorPowerCompare 𝒪 h𝒪 L n]
  rfl

/-- **The homogeneous product of the section ring of Stacks Tag 01CV is the multiplication of the
Laurent algebra of Stacks Tag 01CU**, over the terminal object of the site. The two differ only in
their target degree — `((n + m : ℕ) : ℤ)` against `(n : ℤ) + (m : ℤ)` — and
`Stacks.SheafOfModules.sectionRingMul` carries the transport between them, which is a transport
along a definitional equality and so discharged by
`Stacks.SheafOfModules.TensorPower.heq_reindex`. -/
theorem sectionRingMul_eq_mulBilinear (n m : ℕ)
    (s : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (m : ℤ)).val.obj (op (⊤_ C))) :
    Stacks.SheafOfModules.sectionRingMul 𝒪 h𝒪 L n m s t
      = (Stacks.SheafOfModules.TensorPower.mulBilinear 𝒪 h𝒪 L (n : ℤ) (m : ℤ)).app
          (op (⊤_ C)) s t := by
  rw [Stacks.SheafOfModules.TensorPower.mulBilinear_app]
  exact eq_of_heq (Stacks.SheafOfModules.TensorPower.heq_reindex 𝒪 h𝒪 L (op (⊤_ C))
    (Int.natCast_add n m).symm _)

/-- **The degreewise carrier comparison is multiplicative.** The product of a section of degree
`n` and a section of degree `m` in the sense of `Stacks.GradedSections.mul` — the second section
followed by the first whiskered by `m` copies of `L` — is carried to their product in the sense of
`Stacks.SheafOfModules.sectionRingMul`, the coherent multiplication of Stacks Tag 01CU on their
two global sections.

This is the one statement here with mathematical content, and it is
`Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare` over the terminal object, read
through `powSectionsAddEquiv_apply` and `sectionRingMul_eq_mulBilinear`. -/
theorem powSectionsAddEquiv_mul (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    powSectionsAddEquiv 𝒪 h𝒪 L (n + m) (Stacks.GradedSections.mul s t)
      = Stacks.SheafOfModules.sectionRingMul 𝒪 h𝒪 L n m
          (powSectionsAddEquiv 𝒪 h𝒪 L n s) (powSectionsAddEquiv 𝒪 h𝒪 L m t) := by
  refine Eq.trans ?_ (sectionRingMul_eq_mulBilinear 𝒪 h𝒪 L n m
    (powSectionsAddEquiv 𝒪 h𝒪 L n s) (powSectionsAddEquiv 𝒪 h𝒪 L m t)).symm
  rw [powSectionsAddEquiv_apply, powSectionsAddEquiv_apply, powSectionsAddEquiv_apply]
  exact (Stacks.SheafOfModules.Invertible.mulBilinear_tensorPowerCompare 𝒪 h𝒪 L n m
    (op (⊤_ C)) s t).symm

/-! ### The ring isomorphism -/

omit [HasTerminal C] [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L] in
/-- The product of two homogeneous elements of `Stacks.GradedSections.sectionRing`, as a
homogeneous element. The graded ring structure is `Stacks.GradedSections.instGRing`, whose
homogeneous product is `Stacks.GradedSections.mul` by definition. -/
theorem of_mul_of_gradedSections (n m : ℕ) (s : Stacks.GradedSections.powSections L n)
    (t : Stacks.GradedSections.powSections L m) :
    (DirectSum.of _ n s : Stacks.GradedSections.sectionRing L) * DirectSum.of _ m t
      = DirectSum.of _ (n + m) (Stacks.GradedSections.mul s t) :=
  DirectSum.of_mul_of s t

/-- The product of two homogeneous elements of `Stacks.SheafOfModules.sectionRing`, as a
homogeneous element. That ring's graded structure is *chosen*
(`Stacks.SheafOfModules.chosenRingStructure`), so its homogeneous product has to be identified
with `Stacks.SheafOfModules.sectionRingMul` by the defining field of the chosen structure. -/
theorem of_mul_of_sectionRing (n m : ℕ)
    (a : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C)))
    (b : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (m : ℤ)).val.obj (op (⊤_ C))) :
    (DirectSum.of _ n a : Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L) * DirectSum.of _ m b
      = DirectSum.of _ (n + m) (Stacks.SheafOfModules.sectionRingMul 𝒪 h𝒪 L n m a b) := by
  rw [DirectSum.of_mul_of]
  exact congrArg (DirectSum.of _ (n + m))
    ((Stacks.SheafOfModules.chosenRingStructure 𝒪 h𝒪 L).mul_eq n m a b)

/-- **The carrier comparison of `SectionRingComparison.lean` is multiplicative.** Both products
are determined by their values on homogeneous elements and both are biadditive, so this is a
double induction over the direct sums whose only non-formal case is `powSectionsAddEquiv_mul`. -/
theorem sectionRingHom_mul (x y : Stacks.GradedSections.sectionRing L) :
    sectionRingHom 𝒪 h𝒪 L (x * y)
      = sectionRingHom 𝒪 h𝒪 L x * sectionRingHom 𝒪 h𝒪 L y := by
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | of n s =>
      induction y using DirectSum.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | of m t =>
          rw [of_mul_of_gradedSections, sectionRingHom_of, sectionRingHom_of, sectionRingHom_of,
            of_mul_of_sectionRing, powSectionsAddEquiv_mul]
      | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]
  | add x z hx hz => rw [add_mul, map_add, map_add, hx, hz, add_mul]

/-- **The two section rings of an invertible sheaf of modules are isomorphic as rings.** This is
`Stacks.SectionRingProjTheta.sectionRingAddEquiv` with its multiplicativity supplied; the
underlying function is unchanged, so every computation rule of that additive isomorphism applies
verbatim. -/
@[stacks 01CV "the repository's two realisations of the graded ring `Γ_*(X, L)` — the
`Stacks.GradedSections.sectionRing` one on morphisms out of the monoidal unit and the
`Stacks.SheafOfModules.sectionRing` one on honest global sections — are isomorphic as RINGS, and
the isomorphism is graded (`sectionGradedRingHom`)"]
def sectionRingEquiv :
    Stacks.GradedSections.sectionRing L ≃+* Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L :=
  { sectionRingAddEquiv 𝒪 h𝒪 L with map_mul' := sectionRingHom_mul 𝒪 h𝒪 L }

/-- The ring isomorphism has the additive isomorphism of `SectionRingComparison.lean` as its
underlying additive map, so that every statement proved there — in particular
`Stacks.SectionRingProjTheta.map_summand_eq_sectionRingGrading` — is a statement about it. -/
theorem sectionRingEquiv_toAddEquiv :
    (sectionRingEquiv 𝒪 h𝒪 L).toAddEquiv = sectionRingAddEquiv 𝒪 h𝒪 L := rfl

/-- The ring isomorphism on a homogeneous element. -/
@[simp]
theorem sectionRingEquiv_of (n : ℕ) (s : Stacks.GradedSections.powSections L n) :
    sectionRingEquiv 𝒪 h𝒪 L (DirectSum.of _ n s)
      = DirectSum.of _ n (powSectionsAddEquiv 𝒪 h𝒪 L n s) :=
  sectionRingHom_of 𝒪 h𝒪 L n s

/-- The inverse ring isomorphism on a homogeneous element. -/
@[simp]
theorem sectionRingEquiv_symm_of (n : ℕ)
    (s : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C))) :
    (sectionRingEquiv 𝒪 h𝒪 L).symm (DirectSum.of _ n s)
      = DirectSum.of _ n ((powSectionsAddEquiv 𝒪 h𝒪 L n).symm s) :=
  sectionRingHomInv_of 𝒪 h𝒪 L n s

/-! ### Schemes -/

section Scheme

-- `_root_.` is load-bearing: this file's imports bring `Stacks.AlgebraicGeometry` into scope, and
-- inside `namespace Stacks.SectionRingProjTheta` a bare `open AlgebraicGeometry` resolves to that
-- namespace instead of the root one, leaving `Scheme` unknown.
open _root_.AlgebraicGeometry

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

-- Tag 01CU's invertibility class on a scheme, reinstated from `SectionRingComparison.lean`:
-- instance search does not cross the two spellings of the structure sheaf that a scheme puts in
-- play, so that file supplies the class by hand and this one puts it back in force.
attribute [local instance] schemeStacksIsInvertible

variable {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-- Tensoring on the right by `M` is an equivalence, stated at the structure-sheaf spelling that
`Stacks.SheafOfModules.sectionRingGradedRing` asks for. The generic instance
`Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible` does not fire at a goal
about a scheme — `AlgebraicGeometry.Scheme.Modules` is not unfolded at instance transparency — so
the crossing is paid once here, by the defeq check of `:=`, exactly as
`Stacks.SheafOfModules.tensorRightEquiv` pays it for the `sectionSiteRing` spelling. Without it
the section ring of Tag 01CV has no multiplication at this spelling at all. -/
local instance schemeTensorRightEquiv :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        (⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
            (forget₂ CommRingCat RingCat)
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩)).flip.obj
      M).IsEquivalence :=
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- The graded ring structure of Tag 01CV on the right-hand section ring, reinstated at the scheme
spelling for the same reason as `schemeTensorRightEquiv`. This is the same accommodation
`Stacks.SheafOfModules.sectionSiteRing`'s own file makes. -/
local instance schemeSectionGCommRing : DirectSum.GCommRing
    (fun n : ℕ => (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M (n : ℤ)).val.obj
        (op (⊤_ (TopologicalSpace.Opens ↥X)))) :=
  Stacks.SheafOfModules.sectionRingGradedRing X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- The internal grading of Tag 01CV's section ring is a graded ring structure, reinstated at the
scheme spelling for the same reason as `schemeTensorRightEquiv`. -/
local instance schemeSectionRingGradingGradedRing : GradedRing
    (Stacks.SheafOfModules.sectionRingGrading X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M) :=
  Stacks.SheafOfModules.sectionRingGradingGradedRing X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- **The two section rings of an invertible `𝒪_X`-module on a scheme are isomorphic as rings.**
On the left, the ring `Stacks.AmpleFiniteAvoidance.grading` grades and
`Stacks.SectionRingProjMorphism.projHomOfIsAmple` takes `Proj` of; on the right, the ring the
graded sections of Stacks Tag 01PW are taken over. -/
def schemeSectionRingEquiv :
    Stacks.GradedSections.sectionRing M ≃+*
      Stacks.SheafOfModules.sectionRing X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M :=
  sectionRingEquiv X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- **The ring isomorphism, at the spelling of the structure sheaf that Stacks Tag 01PW uses.**
`Stacks.SheafOfModules.sectionSiteRing` and `Stacks.SheafOfModules.sectionSiteSheaf` are how
`Stacks.SheafOfModules.sectionLocalizationMap` and the two parts of Tag 01PW name the site and its
structure sheaf, and the terminal object of `Opens X` is instance-dependent; this declaration
typechecks exactly when the `HasTerminal (Opens X)` instance in force here is the one Tag 01PW was
elaborated with, so that the ring below is the ring that tag's localizations are formed over. -/
def sectionSiteSectionRingEquiv :
    Stacks.GradedSections.sectionRing M ≃+*
      Stacks.SheafOfModules.sectionRing (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M :=
  schemeSectionRingEquiv M

/-- **The ring isomorphism is an isomorphism of *graded* rings**, from the family `Proj` is taken
of — `Stacks.AmpleFiniteAvoidance.grading`, which
`Stacks.TwistedSections.sectionGrading_eq_ampleGrading` identifies with the family the canonical
morphism to `Proj` is stated over — to the family Tag 01PW's localizations are formed at. The
degree condition is `Stacks.SectionRingProjTheta.map_grading_eq_sectionRingGrading` read as an
inclusion. -/
def sectionGradedRingHom :
    Stacks.AmpleFiniteAvoidance.grading M →+*ᵍ
      Stacks.SheafOfModules.sectionRingGrading (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M where
  toRingHom := (sectionSiteSectionRingEquiv M).toRingHom
  map_mem := by
    rintro i x ⟨s, rfl⟩
    exact ⟨powSectionsAddEquiv X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M i s,
      (sectionRingEquiv_of X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M i s).symm⟩

/-- The inverse of `Stacks.SectionRingProjTheta.sectionGradedRingHom`, as a homomorphism of graded
rings. -/
def sectionGradedRingHomInv :
    Stacks.SheafOfModules.sectionRingGrading (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M →+*ᵍ
      Stacks.AmpleFiniteAvoidance.grading M where
  toRingHom := (sectionSiteSectionRingEquiv M).symm.toRingHom
  map_mem := by
    rintro i y ⟨t, rfl⟩
    exact ⟨(powSectionsAddEquiv X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M i).symm t,
      (sectionRingEquiv_symm_of X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M i t).symm⟩

/-- `Stacks.SectionRingProjTheta.sectionGradedRingHomInv` is a left inverse of
`Stacks.SectionRingProjTheta.sectionGradedRingHom`. -/
theorem sectionGradedRingHomInv_comp :
    (sectionGradedRingHomInv M).comp (sectionGradedRingHom M)
      = GradedRingHom.id (Stacks.AmpleFiniteAvoidance.grading M) :=
  GradedRingHom.ext fun x => (sectionSiteSectionRingEquiv M).symm_apply_apply x

/-- `Stacks.SectionRingProjTheta.sectionGradedRingHomInv` is a right inverse of
`Stacks.SectionRingProjTheta.sectionGradedRingHom`. -/
theorem sectionGradedRingHom_comp :
    (sectionGradedRingHom M).comp (sectionGradedRingHomInv M)
      = GradedRingHom.id (Stacks.SheafOfModules.sectionRingGrading
          (Stacks.SheafOfModules.sectionSiteRing X) (Stacks.SheafOfModules.sectionSiteSheaf X) M) :=
  GradedRingHom.ext fun x => (sectionSiteSectionRingEquiv M).apply_symm_apply x

/-- The hypothesis of `AlgebraicGeometry.Proj.map` for
`Stacks.SectionRingProjTheta.sectionGradedRingHom`: the irrelevant ideal of Tag 01PW's graded ring
is covered by the image of the irrelevant ideal of the ring `Proj` is taken of. It is automatic
for an isomorphism, by `Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id`. -/
theorem irrelevant_le_map_sectionGradedRingHom :
    HomogeneousIdeal.irrelevant (Stacks.SheafOfModules.sectionRingGrading
        (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M)
      ≤ (HomogeneousIdeal.irrelevant (Stacks.AmpleFiniteAvoidance.grading M)).map
          (sectionGradedRingHom M) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (sectionGradedRingHom_comp M)

/-- The same hypothesis for `Stacks.SectionRingProjTheta.sectionGradedRingHomInv`. -/
theorem irrelevant_le_map_sectionGradedRingHomInv :
    HomogeneousIdeal.irrelevant (Stacks.AmpleFiniteAvoidance.grading M)
      ≤ (HomogeneousIdeal.irrelevant (Stacks.SheafOfModules.sectionRingGrading
          (Stacks.SheafOfModules.sectionSiteRing X)
          (Stacks.SheafOfModules.sectionSiteSheaf X) M)).map (sectionGradedRingHomInv M) :=
  Stacks.RelativeProj.irrelevant_le_map_of_comp_eq_id _ _ (sectionGradedRingHomInv_comp M)

/-- **`Proj` of Tag 01PW's graded ring is `Proj Γ_*(X, L)`.** This is `AlgebraicGeometry.Proj.map`
of the graded ring isomorphism in both directions, the two composites being the identity by
`AlgebraicGeometry.Proj.map_comp`, `AlgebraicGeometry.Proj.map_congr` and
`AlgebraicGeometry.Proj.map_id`.

The right-hand side is the scheme `Stacks.SectionRingProjMorphism.projHomOfIsAmple` maps into and
`Stacks.AmpleFiniteAvoidance` grades; the left-hand side is `Proj` of the ring
`Stacks.SheafOfModules.sectionLocalizationMap` — the comparison map of Tag 0B5L, whose bijectivity
is Tag 01PW part (2) — localizes. Producing it needs the *products* to be identified and not only
the carriers: `AlgebraicGeometry.Proj.map` consumes a `GradedRingHom`. -/
def projIso :
    AlgebraicGeometry.Proj (Stacks.SheafOfModules.sectionRingGrading
        (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M)
      ≅ AlgebraicGeometry.Proj (Stacks.AmpleFiniteAvoidance.grading M) where
  hom := Proj.map (sectionGradedRingHom M) (irrelevant_le_map_sectionGradedRingHom M)
  inv := Proj.map (sectionGradedRingHomInv M) (irrelevant_le_map_sectionGradedRingHomInv M)
  hom_inv_id :=
    (Proj.map_comp (sectionGradedRingHomInv M) (sectionGradedRingHom M)
          (irrelevant_le_map_sectionGradedRingHomInv M)
          (irrelevant_le_map_sectionGradedRingHom M)).symm.trans
      ((Proj.map_congr (sectionGradedRingHom_comp M) _ _).trans Proj.map_id)
  inv_hom_id :=
    (Proj.map_comp (sectionGradedRingHom M) (sectionGradedRingHomInv M)
          (irrelevant_le_map_sectionGradedRingHom M)
          (irrelevant_le_map_sectionGradedRingHomInv M)).symm.trans
      ((Proj.map_congr (sectionGradedRingHomInv_comp M) _ _).trans Proj.map_id)

end Scheme

end Stacks.SectionRingProjTheta

end
