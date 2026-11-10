module

public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistIntegerLocalComparison
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist

/-!
# The degree-zero normalization of Tag 0B5I's comparison morphism

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `ℱ` be an arbitrary sheaf of
`𝒪_X`-modules and let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the integer-graded `S`-module of twisted
global sections of Tag 03GK. Tag 0B5I's last assertion about the comparison morphism
`M̃ ⟶ ℱ` is that **in degree zero it is the identity of `Γ(X, ℱ)`**: the source reads the
degree-zero part `M_0 = Γ(X, ℱ(0))` of the module through the identification `ℱ(0) = ℱ`, and
asserts that the global section of `M̃` attached to an element of `M_0` by Tag 01M7 is carried to
the corresponding global section of `ℱ`.

This file supplies the identification and proves that assertion.

## The identification `ℱ(0) ≅ ℱ`

`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` is `𝒪_X(0) ≅ 𝒪_X`, but
`ℱ(0)` is `ℱ ⊗ 𝒪_X(0)`, so the comparison the normalization needs is that trivialization
tensored into the second factor of `ℱ ⊗ 𝒪_X(0)` and then cancelled by the right unit constraint
of the sheafified tensor product. That composite,
`Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization.twistZeroCancelIso`, is built here.

It is built in an arbitrary twisting degree `c` together with a proof that `c` vanishes, rather
than in the degree `0` alone, and this is not decoration: multiplication by the trivializing
section `f ^ n` on a chart,
`Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection`, produces a section of the twist
in the degree `n · d` for the degree `d` of the homogeneous element `f`, so at `n = 0` the
twisting degree reaching the normalization is `0 · d`, which is equal to `0` but not
definitionally so. The degree-indexed form is what lets the same isomorphism be used on both
sides of the chart computation.

The analogous identification in the tensor-algebra setting,
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit` and
`Stacks.AlgebraicGeometry.ThetaGlobal.twistZeroIsoUnit`, is a different object: those are
isomorphisms of the zeroth twist of the *structure sheaf* with the structure sheaf, on `Proj 𝒮`
and on a degree-`d` open respectively, whereas the composite built here is an isomorphism of
the zeroth twist of an *arbitrary* sheaf of modules with that sheaf.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization.twistingSheafIsoUnitOfEq`:
  `𝒪_X(c) ≅ 𝒪_X` for a vanishing degree `c`.
* `Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization.twistZeroCancelIso`:
  **`ℱ(c) ≅ ℱ` for a vanishing degree `c`** — the identification the normalization is read
  through.

## Main results

* `twistZeroCancelIso_hom_val_app_mulTrivSection` and
  `mulTrivSection_twistZeroCancelIso_hom_val_app`: **the identification is inverse to
  multiplication by the trivializing section `f ^ 0`** on the sections over an open inside
  `D₊(f)`. This is the compatibility that makes the identification the right one: `f ^ 0` is the
  section `1`, and the identification is the right unit constraint.
* `integerComparison_degreeZeroToGlobalSections`: the comparison morphism carries the global
  section of `M̃` attached to a degree-zero element `m` to the global section of `ℱ` corresponding
  to `m`.
* `integerComparison_degreeZeroToGlobalSections_id`: **Tag 0B5I's degree-zero normalization** —
  the same statement read as the assertion that the comparison induces the identity of
  `Γ(X, ℱ)`. With this the three assertions of Tag 0B5I for the integer-graded module of twisted
  global sections carry no hypotheses:
  `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.existsUnique_comparison` is the morphism
  and its uniqueness, `integerComparison_naturality` is its functoriality in `ℱ`, and this is
  its normalization.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf trivializingSection
  trivializingFun)
open Stacks.AlgebraicGeometry.ProjEulerSequence (twistingSheafZeroIsoUnit
  val_twistingSheafZeroIsoUnit_hom_apply)
open Stacks.AlgebraicGeometry.ProjTwistRestriction (isSheaf_proj mulTrivSection
  injective_hom_val_app bijective_mulTrivSection)
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **`𝒪_X(c) ≅ 𝒪_X` for a vanishing twisting degree `c`.** -/
def twistingSheafIsoUnitOfEq {c : ℤ} (hc : c = 0) :
    twistingSheaf 𝒮 c ≅ SheafOfModules.unit (projRingSheaf 𝒮) :=
  eqToIso (congrArg (twistingSheaf 𝒮) hc) ≪≫ twistingSheafZeroIsoUnit 𝒮

/-- The coordinate of a local section of `𝒪_X(c)`, for a vanishing degree `c`, in the
trivialization `twistingSheafIsoUnitOfEq`: a section of the structure sheaf over the same open.
Its only purpose is to carry the structure-sheaf type ascription, so that it can be used as a
scalar. -/
def twistZeroCoord {c : ℤ} (hc : c = 0) (W : Opens (ProjectiveSpectrum.top 𝒮))
    (s : (twistingSheaf 𝒮 c).val.obj (op W)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W) :=
  (twistingSheafIsoUnitOfEq 𝒮 hc).hom.val.app (op W) s

/-- A section of `𝒪_X(c)` all of whose values are `1` has coordinate `1`. -/
theorem twistZeroCoord_eq_one {c : ℤ} (hc : c = 0)
    (W : Opens (ProjectiveSpectrum.top 𝒮)) (s : (twistingSheaf 𝒮 c).val.obj (op W))
    (hs : ∀ x : W, (s.1 x) = 1) :
    twistZeroCoord 𝒮 hc W s = 1 := by
  change (twistingSheafIsoUnitOfEq 𝒮 hc).hom.val.app (op W) s =
    (1 : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W))
  subst hc
  have h : (twistingSheafIsoUnitOfEq 𝒮 (rfl : (0 : ℤ) = 0)).hom.val.app (op W) s =
      (twistingSheafZeroIsoUnit 𝒮).hom.val.app (op W) s := by
    simp [twistingSheafIsoUnitOfEq]
  rw [h]
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  rw [val_twistingSheafZeroIsoUnit_hom_apply, hs x]
  simp

variable (F : SheafOfModules.{u} (projRingSheaf 𝒮))

/-- **`ℱ(c) ≅ ℱ` for a vanishing twisting degree `c`**: the trivialization of `𝒪_X(c)` tensored
into the first factor, followed by the right unit constraint of the sheafified tensor
product. -/
def twistZeroCancelIso {c : ℤ} (hc : c = 0) : twistSheafOfModules 𝒮 F c ≅ F :=
  Stacks.SheafOfModules.TensorPower.tensorSheafMapIso
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮) (Iso.refl F)
      (twistingSheafIsoUnitOfEq 𝒮 hc) ≪≫
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮) F

/-- The value of the cancellation isomorphism on the image of a pure tensor `t ⊗ s` under the
sheafification unit is the scalar multiple of `t` by the coordinate of `s`. -/
theorem twistZeroCancelIso_hom_val_app_toSheafify {c : ℤ} (hc : c = 0)
    (W : Opens (ProjectiveSpectrum.top 𝒮)) (t : F.val.obj (op W))
    (s : (twistingSheaf 𝒮 c).val.obj (op W)) :
    (twistZeroCancelIso 𝒮 F hc).hom.val.app (op W)
        ((Stacks.SheafOfModules.TensorSheafification.toSheafify
            (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮)
            (F.val ⊗ (twistingSheaf 𝒮 c).val)).app (op W)
          (t ⊗ₜ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)] s)) =
      twistZeroCoord 𝒮 hc W s • t := by
  refine Eq.trans (congrArg (fun z ↦ (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮) F).hom.val.app (op W) z)
      (Stacks.SheafOfModules.sheafify_map_toSheafify_app
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮)
        ((SheafOfModules.forget _).map (Iso.refl F).hom ⊗ₘ
          (SheafOfModules.forget _).map (twistingSheafIsoUnitOfEq 𝒮 hc).hom) (op W)
        (t ⊗ₜ[(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)] s))) ?_
  exact Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso_hom_app
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_proj 𝒮) F (op W) t _

variable {f : S} {d : ℕ}

/-- **The trivializing section `f ^ 0` is the section `1`.** -/
theorem trivializingSection_zero_apply (hf : f ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (x : W) :
    ((trivializingSection 𝒮 hf 0 hW).1 x) = 1 := by
  change trivializingFun 𝒮 0 hW x = 1
  rw [trivializingFun, ← Localization.mk_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- **Dividing `t ⊗ f ^ 0` by the trivialization gives `t` back**, on all of `Proj 𝒮`. -/
theorem twistZeroCancelIso_hom_val_app_mulTrivSection (hf : f ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : F.val.obj (op W)) :
    (twistZeroCancelIso 𝒮 F (zero_mul (d : ℤ))).hom.val.app (op W)
        (mulTrivSection 𝒮 hf 0 F hW t) = t := by
  refine Eq.trans (twistZeroCancelIso_hom_val_app_toSheafify 𝒮 F (zero_mul (d : ℤ)) W t
    (trivializingSection 𝒮 hf 0 hW)) ?_
  rw [twistZeroCoord_eq_one 𝒮 (zero_mul (d : ℤ)) W _
    (trivializingSection_zero_apply 𝒮 hf hW)]
  exact one_smul _ t

/-- **Multiplying by `f ^ 0` undoes the cancellation isomorphism.** -/
theorem mulTrivSection_twistZeroCancelIso_hom_val_app (hf : f ∈ 𝒮 d)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (u : (twistSheafOfModules 𝒮 F ((0 : ℤ) * d)).val.obj (op W)) :
    mulTrivSection 𝒮 hf 0 F hW
        ((twistZeroCancelIso 𝒮 F (zero_mul (d : ℤ))).hom.val.app (op W) u) = u :=
  injective_hom_val_app (twistZeroCancelIso 𝒮 F (zero_mul (d : ℤ))) (op W)
    (twistZeroCancelIso_hom_val_app_mulTrivSection 𝒮 F hf hW _)

/-! ### The degree-zero normalization -/

section Normalization

open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedSectionsComponent TwistedGlobalSectionsModule twistedGlobalSectionsAssociatedSheaf
  isTwistedSectionsSMul_twistedGlobalSectionsModule)
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  comparison_degreeZeroToGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistIntegerComparison (degreeComponent degreeComponent_of
  localComparison localComparison_restrict integerComparison positiveChartHom_eq_chartHom
  mulTrivSection_chartHom)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections
  degreeZeroToGlobalSections_basicOpen)

/-- **Multiplying by `f ^ 0` the restriction of the global section of `ℱ` attached to a
degree-zero twisted global section returns the restriction of that section.**

The twisting degree is kept as an arbitrary vanishing `c`, with multiplication by `f ^ 0`
abstracted into a function `μ` whose only property is that it undoes the cancellation
isomorphism. That is what lets the equation be proved at `c = 0`, where the identification of
the twist with `ℱ` is the one the statement names, and then be used at `c = 0 · d`, where
`Stacks.AlgebraicGeometry.ProjTwistRestriction.mulTrivSection` lives. -/
private theorem mulTrivSection_restrict_aux {c : ℤ} (hc : c = 0)
    (W : Opens (ProjectiveSpectrum.top 𝒮))
    (μ : (F.val.obj (op W)) → ((twistSheafOfModules 𝒮 F c).val.obj (op W)))
    (hμ : ∀ u, μ ((twistZeroCancelIso 𝒮 F hc).hom.val.app (op W) u) = u)
    (x : twistedGlobalSections 𝒮 F) :
    μ (F.val.map (homOfLE (le_top : W ≤ ⊤)).op
        ((twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).hom.val.app (op ⊤)
          (degreeComponent 𝒮 F 0 x))) =
      (twistSheafOfModules 𝒮 F c).val.map (homOfLE (le_top : W ≤ ⊤)).op
        (degreeComponent 𝒮 F c x) := by
  subst hc
  refine Eq.trans (congrArg μ (PresheafOfModules.naturality_apply
    (twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).hom.val (homOfLE (le_top : W ≤ ⊤)).op
    (degreeComponent 𝒮 F 0 x)).symm) ?_
  exact hμ _

variable (D : TwistedGlobalSectionsModule 𝒮 F)

/-- **The chart value of the comparison on the global section of a degree-zero element, times
the trivializing section `f ^ 0`, is the restriction of that element.** This is
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.mulTrivSection_chartHom` at `n = 0`, whose
fraction hypothesis is Tag 01M7's `degreeZeroToGlobalSections_basicOpen`. -/
private theorem mulTrivSection_localComparison_degreeZero
    (m : twistedGlobalSectionsGrading 𝒮 F 0) (p : PositiveElem 𝒮)
    (hle : positiveBasicOpen 𝒮 p ≤ ⊤) {e : ℕ} (he : 0 < e) (hp : (p.1 : S) ∈ 𝒮 e) :
    letI := D.moduleInst
    letI := D.gradedSMul
    mulTrivSection 𝒮 hp 0 F (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (p.1 : S)))
        (localComparison 𝒮 F D p
          ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE hle).op
            (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) m))) =
      (twistSheafOfModules 𝒮 F ((0 : ℤ) * e)).val.map (homOfLE hle).op
        (degreeComponent 𝒮 F ((0 : ℤ) * e) m.1) := by
  let := D.moduleInst
  let := D.gradedSMul
  have hsmul := isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F D
  refine Eq.trans (congrArg (mulTrivSection 𝒮 hp 0 F (le_refl _))
    (congrFun (congrArg (fun φ => (ModuleCat.Hom.hom φ).toFun)
      (positiveChartHom_eq_chartHom 𝒮 F hsmul p hp he)) _)) ?_
  refine mulTrivSection_chartHom 𝒮 F hsmul hp he _ 0 m.1 (by simp) ?_
  exact congrArg Subtype.val
    (degreeZeroToGlobalSections_basicOpen 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hp he m)

/-- **The degree-zero normalization on one chart.** -/
private theorem localComparison_degreeZeroToGlobalSections
    (m : twistedGlobalSectionsGrading 𝒮 F 0) (p : PositiveElem 𝒮)
    (hle : positiveBasicOpen 𝒮 p ≤ ⊤) :
    letI := D.moduleInst
    letI := D.gradedSMul
    localComparison 𝒮 F D p
        ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE hle).op
          (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) m)) =
      F.val.map (homOfLE hle).op
        ((twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).hom.val.app
          (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) (degreeComponent 𝒮 F 0 m.1)) := by
  let := D.moduleInst
  let := D.gradedSMul
  obtain ⟨e, he, hp⟩ := p.2
  refine (bijective_mulTrivSection 𝒮 hp (0 : ℤ) F
    (le_refl (ProjectiveSpectrum.basicOpen 𝒮 (p.1 : S)))).injective ?_
  refine Eq.trans (mulTrivSection_localComparison_degreeZero 𝒮 F D m p hle he hp) ?_
  exact (mulTrivSection_restrict_aux 𝒮 F (zero_mul (e : ℤ))
    (positiveBasicOpen 𝒮 p) (mulTrivSection 𝒮 hp 0 F (le_refl _))
    (mulTrivSection_twistZeroCancelIso_hom_val_app 𝒮 F hp (le_refl _)) m.1).symm

/-- **Tag 0B5I's degree-zero normalization: the comparison morphism induces the identity on
`Γ(X, ℱ)`.**

A degree-zero element `m` of `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` is a global section of `ℱ(0)`, and gives
a global section of `M̃` by Tag 01M7. The comparison morphism carries that global section to the
global section of `ℱ` that corresponds to `m` under the identification `ℱ(0) ≅ ℱ` of
`twistZeroCancelIso`. Since that identification is an isomorphism, this says exactly that the
degree-zero part of the comparison is the identity of `Γ(X, ℱ)`.

Nothing is hypothesised. On the standard open `D₊(f)` of a positive-degree homogeneous element
the global section of `M̃` is the fraction `m / f ^ 0`, so the chart comparison takes it to the
section whose product with the trivializing section `f ^ 0` is the restriction of `m`; and the
restriction of the global section named on the right has the same property, because `f ^ 0` is
the section `1` and the cancellation isomorphism is the right unit constraint. Multiplication by
the trivializing section being injective, the two agree on every chart, hence everywhere.

The proof is `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_degreeZeroToGlobalSections`
— the conditional form, which quantifies over the standard-open comparison maps and over the
global section the comparison produces — instantiated at
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.localComparison`, its compatibility
`localComparison_restrict`, and the section named by `twistZeroCancelIso`. -/
theorem integerComparison_degreeZeroToGlobalSections (m : twistedGlobalSectionsGrading 𝒮 F 0) :
    letI := D.moduleInst
    letI := D.gradedSMul
    (integerComparison 𝒮 F D).val.app (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
        (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) m) =
      (twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).hom.val.app
        (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) (degreeComponent 𝒮 F 0 m.1) := by
  let := D.moduleInst
  let := D.gradedSMul
  exact comparison_degreeZeroToGlobalSections 𝒮 F D (localComparison 𝒮 F D)
    (localComparison_restrict 𝒮 F D) m _ rfl _
    (localComparison_degreeZeroToGlobalSections 𝒮 F D m)

/-- **Tag 0B5I: in degree zero the comparison morphism is the identity of `Γ(X, ℱ)`.**

Let `t` be a global section of `ℱ`. Under the identification `ℱ(0) ≅ ℱ` of `twistZeroCancelIso`
it is a global section of `ℱ(0)`, that is, a degree-zero element of
`M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`; the global section of `M̃` it defines by Tag 01M7 is carried by Tag
0B5I's comparison morphism back to `t`. This is the source's assertion that, read through
`Γ(X, ℱ(0)) = Γ(X, ℱ)`, the comparison induces the identity on `Γ(X, ℱ)`.

Nothing is hypothesised: the identification is the composite of the trivialization
`𝒪_X(0) ≅ 𝒪_X` of Tag 01MN with the right unit constraint of the tensor product, and the local
maps are the chart comparisons of
`Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.chartHom`. -/
theorem integerComparison_degreeZeroToGlobalSections_id
    (t : F.val.obj (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))) :
    letI := D.moduleInst
    letI := D.gradedSMul
    (integerComparison 𝒮 F D).val.app (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
        (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
          ⟨DirectSum.of (fun k : ℤ => twistedSectionsComponent 𝒮 F k) 0
              ((twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).inv.val.app
                (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) t),
            (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => twistedSectionsComponent 𝒮 F k) 0
              _).mpr ⟨_, rfl⟩⟩) = t := by
  let := D.moduleInst
  let := D.gradedSMul
  refine Eq.trans (integerComparison_degreeZeroToGlobalSections 𝒮 F D _) ?_
  refine Eq.trans (congrArg ((twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).hom.val.app
      (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))) (degreeComponent_of 𝒮 F 0 _)) ?_
  exact Stacks.SheafOfModules.hom_val_app_inv_val_app
    (twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0))
    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) t

end Normalization

end Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization

end
