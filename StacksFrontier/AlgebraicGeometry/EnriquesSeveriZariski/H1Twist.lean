module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.AlgebraicGeometry.CohomologyShiftInjectivity.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionTwist
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.OverFieldAction
public import StacksFrontier.Data.Int.EventuallyBelow
public import StacksFrontier.LinearAlgebra.InjectiveTower

/-!
# Multiplication by a regular section is injective on `H¹` in all very negative twists

Let `k` be a field, `X` a proper scheme over `k`, `ℒ` an ample invertible `𝒪_X`-module and `ℱ` a
coherent `𝒪_X`-module whose stalk has depth at least two at every closed point.  Let `s` be a
global section of `ℒ^{⊗ n}` which does not vanish at any associated point of `ℱ`.  Then

`H¹(X, ℱ ⊗ ℒ^{⊗ j}) ⟶ H¹(X, ℱ ⊗ ℒ^{⊗ (n + j)})`

is injective for every `j ≪ 0`.

This is the step of [Stacks, Tag 0FD8] which feeds [Stacks, Tag 0FD7] into the long exact
sequence.  The three inputs are all on hand: multiplication by `s` is a monomorphism
(`Stacks.Divisors.mono_actionPow_of_nonvanishing`), its cokernel is a twist of the **one** module
`Stacks.EnriquesSeveriZariski.cokernelModule` (`Stacks.Divisors.cokernelActionPowIso`), and that
module has no closed associated point
(`Stacks.Divisors.notMem_associatedPoints_cokernel_actionPow`), so 0FD7 kills its degree-zero
cohomology in all sufficiently negative twists at once.

## Main results

* `Stacks.EnriquesSeveriZariski.cokernelModule`: the module whose twists are the cokernels of
  multiplication by `s`, together with `isCoherent_cokernelModule` and
  `notMem_associatedPoints_cokernelModule`.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_isZero_cohomologyOverField_cokernel_actionPow`:
  the cokernel has vanishing `H⁰` in all sufficiently negative twists.
* `Stacks.EnriquesSeveriZariski.exists_forall_le_injective_cohomologyOverFieldMap_actionPow`:
  **multiplication by `s` is injective on `H¹` in all sufficiently negative twists.**

## Implementation notes

`Stacks.Divisors.cokernelActionPowIso` is stated at `Stacks.Divisors.twistPow`, which is
`Stacks.Cohomology.TwistedGradedModule.twist` by `rfl`; that is the spelling 0FD7 was restated
at in `exists_forall_le_isZero_cohomologyOverField_zero_twistedGradedModuleTwist` (in the
namespace `Stacks.EnriquesSeveriZariski`), so no comparison of twists intervenes.

The identification of `cokernelModule` with the degree-zero cokernel uses
`Stacks.SheafOfModules.TensorPower.tensorPower_zero`, which makes `ℒ^{⊗ 0}` the structure sheaf
by `rfl`, followed by the right unit constraint of the tensor product.  That is the only place
where a particular degree is singled out, and it is what makes coherence and the
associated-points condition for `cokernelModule` follow from the statements already proved about
the cokernel.

## References

* [Stacks Project, Tag 0FD8](https://stacks.math.columbia.edu/tag/0FD8)
* [Stacks Project, Tag 0FD7](https://stacks.math.columbia.edu/tag/0FD7)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules

universe u

namespace Stacks.EnriquesSeveriZariski

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The module whose twists are the cokernels of multiplication by `s`.**  It is
`coker(𝒪_X ⟶ ℒ^{⊗ n}) ⊗ ℱ`, and `Stacks.Divisors.cokernelActionPowIso` identifies its `j`-th
twist with the cokernel of multiplication by `s` on `ℱ ⊗ ℒ^{⊗ j}`, for every `j`. -/
abbrev cokernelModule (F : X.Modules) (n : ℤ) (s : Stacks.Divisors.powSection L n) : X.Modules :=
  Scheme.Modules.tensorObj (cokernel (Stacks.Divisors.powSectionHom L n s)) F

/-- The degree-zero cokernel of multiplication by `s` is `cokernelModule`: the zeroth tensor
power is the structure sheaf, and tensoring with it changes nothing. -/
def cokernelModuleIso (F : X.Modules) (n : ℤ) (s : Stacks.Divisors.powSection L n) :
    cokernel (Stacks.Divisors.actionPow L F n 0 s) ≅ cokernelModule L F n s :=
  Stacks.Divisors.cokernelActionPowIso L F n 0 s ≪≫
    Invertible.tensorProductRightUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (cokernelModule L F n s)

/-- `cokernelModule` is coherent: it is isomorphic to the cokernel of a morphism of coherent
modules. -/
theorem isCoherent_cokernelModule [AlgebraicGeometry.IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (n : ℤ) (s : Stacks.Divisors.powSection L n) :
    (cokernelModule L F n s).IsCoherent :=
  AlgebraicGeometry.isCoherent_of_moduleIso (cokernelModuleIso L F n s)
    (Stacks.Divisors.isCoherent_cokernel_actionOf L F n 0 s)

/-- **No closed point is an associated point of `cokernelModule`**, when `ℱ` has depth at least
two at every closed point and `s` does not vanish at any associated point of `ℱ`. -/
theorem notMem_associatedPoints_cokernelModule [AlgebraicGeometry.IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (n : ℤ) (s : Stacks.Divisors.powSection L n)
    (hs : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
        (AlgebraicGeometry.restrictTerminalTopEquiv _ s))
    (hdepth : ∀ y : X, IsClosed ({y} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y))
    (y : X) (hy : IsClosed ({y} : Set X)) :
    y ∉ Stacks.Divisors.associatedPoints (cokernelModule L F n s) := by
  rw [← Stacks.Divisors.associatedPoints_congr (cokernelModuleIso L F n s)]
  exact Stacks.Divisors.notMem_associatedPoints_cokernel_actionPow L F n 0 s
    (Stacks.Divisors.mono_actionPow_of_nonvanishing L F n 0 s hs) (hdepth y hy)

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The cokernel of multiplication by `s` has vanishing degree-zero cohomology in all
sufficiently negative twists.**  This is [Stacks, Tag 0FD7] applied once, to `cokernelModule`;
the cokernels in every degree are its twists. -/
theorem exists_forall_le_isZero_cohomologyOverField_cokernel_actionPow
    (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsCoherent] (n : ℤ)
    (s : Stacks.Divisors.powSection L n)
    (hs : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
        (AlgebraicGeometry.restrictTerminalTopEquiv _ s))
    (hdepth : ∀ y : X, IsClosed ({y} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y)) :
    ∃ j₀ : ℤ, ∀ j : ℤ, j ≤ j₀ →
      IsZero (AlgebraicGeometry.cohomologyOverField k f
        (cokernel (Stacks.Divisors.actionPow L F n j s)) 0) := by
  have : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isCoherent_cokernelModule L F n s
  obtain ⟨j₀, hj₀⟩ :=
    exists_forall_le_isZero_cohomologyOverField_zero_twistedGradedModuleTwist L k f hL
      (cokernelModule L F n s)
      (fun y hy => notMem_associatedPoints_cokernelModule L F n s hs hdepth y hy)
  exact ⟨j₀, fun j hj => (hj₀ j hj).of_iso
    (AlgebraicGeometry.cohomologyOverFieldIso k f
      (Stacks.Divisors.cokernelActionPowIso L F n j s) 0)⟩

/-- **Multiplication by a global section of `ℒ^{⊗ n}` that does not vanish at any associated
point of `ℱ` is injective on `H¹` in all sufficiently negative twists.**  The multiplication is a
monomorphism, so it sits in a short exact sequence whose third term is the cokernel; the
cokernel's `H⁰` vanishes in all sufficiently negative twists, and the long exact sequence turns
that into injectivity one degree up. -/
theorem exists_forall_le_injective_cohomologyOverFieldMap_actionPow
    (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsCoherent] (n : ℤ)
    (s : Stacks.Divisors.powSection L n)
    (hs : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
        (AlgebraicGeometry.restrictTerminalTopEquiv _ s))
    (hdepth : ∀ y : X, IsClosed ({y} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y)) :
    ∃ j₀ : ℤ, ∀ j : ℤ, j ≤ j₀ → Function.Injective
      (AlgebraicGeometry.cohomologyOverFieldMap k f (Stacks.Divisors.actionPow L F n j s) 1) := by
  have : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨j₀, hj₀⟩ :=
    exists_forall_le_isZero_cohomologyOverField_cokernel_actionPow L k f hL F n s hs hdepth
  refine ⟨j₀, fun j hj => ?_⟩
  have := Stacks.Divisors.mono_actionPow_of_nonvanishing L F n j s hs
  exact AlgebraicGeometry.injective_cohomologyOverFieldMap_succ_of_isZero k f
    (Stacks.Divisors.shortExact_actionOf_of_mono L F n j s) 0 (hj₀ j hj)

/-! ### A section of some positive power regular on `ℱ`

Ampleness supplies, for the finite set of associated points of `ℱ`, a section of some positive
tensor power of `ℒ` not vanishing at any of them ([Stacks, Tag 09NV]).  That statement is written
at `Stacks.Ample.tensorPowModule`, the iterated tensor product, while
`Stacks.SheafOfModules.TwistAction.actionOf` multiplies by a section of
`Stacks.Algebraization.tensorPowScheme`; `Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow`
compares the two families and `Stacks.Ample.nonvanishingLocus_congr` carries the nonvanishing
locus across. -/

/-- **A positive power of `ℒ` has a global section vanishing at no associated point of `ℱ`**, at
the spelling of the tensor power that multiplication on the twists is stated over. -/
theorem exists_regular_powSection [AlgebraicGeometry.IsLocallyNoetherian X] [CompactSpace X]
    (hL : Stacks.Ample.IsAmple X L) (F : X.Modules) [F.IsCoherent] :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ s : Stacks.Divisors.powSection L (e : ℤ),
      ∀ x ∈ Stacks.Divisors.associatedPoints F,
        x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L (e : ℤ))
          (AlgebraicGeometry.restrictTerminalTopEquiv _ s) := by
  obtain ⟨e, he, σ, -, hsub, -⟩ :=
    Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
      (AlgebraicGeometry.associatedPoints_finite F) ⊤ (by simp)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L :=
    Stacks.RelativeVeryAmple.stacksIsInvertible X L
  let bridge : Stacks.Algebraization.tensorPowScheme X L (e : ℤ) ≅
      Stacks.Ample.tensorPowModule X L (e : ℤ) :=
    Stacks.PowerFamilyBridge.tensorPowerIsoTensorPow X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L (e : ℤ)
  refine ⟨e, he,
    (AlgebraicGeometry.restrictTerminalTopEquiv _).symm (bridge.inv.app ⊤ σ), fun x hx => ?_⟩
  have hback : bridge.hom.app ⊤
      (AlgebraicGeometry.restrictTerminalTopEquiv
        (Stacks.Algebraization.tensorPowScheme X L (e : ℤ))
        ((AlgebraicGeometry.restrictTerminalTopEquiv _).symm (bridge.inv.app ⊤ σ))) = σ := by
    rw [AddEquiv.apply_symm_apply]
    exact congrArg (fun φ : Stacks.Ample.tensorPowModule X L (e : ℤ) ⟶
      Stacks.Ample.tensorPowModule X L (e : ℤ) => Scheme.Modules.Hom.app φ ⊤ σ) bridge.inv_hom_id
  rw [← Stacks.Ample.nonvanishingLocus_congr bridge, hback]
  exact hsub hx

/-! ### Comparing the two spellings of the space of sections

`Stacks.Cohomology.TwistCohomologyAction.twistCohomologyAction` takes its multiplying section
over the categorical terminal open `⊤_ (Opens X)`, with scalars restricted along the structure
morphism read there, while `AlgebraicGeometry.globalSectionsOverField` is stated at
`(⊤ : X.Opens)`. `AlgebraicGeometry.restrictTerminalTopEquiv` compares the two groups and
`Stacks.Cohomology.TwistCohomologyAction.baseSection_restrict` makes it `k`-linear. -/

/-- **The two spellings of the `k`-vector space of global sections of `ℒ^{⊗ d}` agree.** -/
def twistSectionSpaceEquiv (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (d : ℤ) :
    Stacks.Cohomology.TwistCohomologyAction.twistSectionSpace k f L d ≃ₗ[k]
      AlgebraicGeometry.globalSectionsOverField k f
        (Stacks.Algebraization.tensorPowScheme X L d) where
  toFun := AlgebraicGeometry.restrictTerminalTopEquiv
    (Stacks.Algebraization.tensorPowScheme X L d)
  invFun := (AlgebraicGeometry.restrictTerminalTopEquiv
    (Stacks.Algebraization.tensorPowScheme X L d)).symm
  left_inv := (AlgebraicGeometry.restrictTerminalTopEquiv _).symm_apply_apply
  right_inv := (AlgebraicGeometry.restrictTerminalTopEquiv _).apply_symm_apply
  map_add' _ _ := map_add _ _ _
  map_smul' c x := by
    have h2 : (ConcreteCategory.hom (X.ringCatSheaf.obj.map (terminal.from (⊤ : X.Opens)).op))
          (Stacks.Cohomology.TwistCohomologyAction.baseSection k f c) =
        Stacks.Cohomology.TwistCohomologyAction.baseScalar k f c :=
      Stacks.Cohomology.TwistCohomologyAction.baseSection_restrict k f c
    have h1 := PresheafOfModules.map_smul (Stacks.Algebraization.tensorPowScheme X L d).val
      (terminal.from (⊤ : X.Opens)).op
      (Stacks.Cohomology.TwistCohomologyAction.baseSection k f c) x
    rwa [h2] at h1

/-! ### Injectivity of the map induced by a morphism with a two-sided inverse -/

/-- The map induced on cohomology by a morphism with a left inverse is injective; this covers the
reindexing comparisons of the twists, whose `IsIso` instance is not found by instance search. -/
theorem injective_cohomologyOverFieldMap_of_inverse (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) {A B : X.Modules} (ψ : A ⟶ B) (χ : B ⟶ A) (h : ψ ≫ χ = 𝟙 A)
    (p : ℕ) : Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f ψ p) := by
  have e : AlgebraicGeometry.cohomologyOverFieldMap k f ψ p ≫
      AlgebraicGeometry.cohomologyOverFieldMap k f χ p = 𝟙 _ := by
    rw [← AlgebraicGeometry.cohomologyOverFieldMap_comp, h,
      AlgebraicGeometry.cohomologyOverFieldMap_id]
  exact Function.LeftInverse.injective (g := AlgebraicGeometry.cohomologyOverFieldMap k f χ p)
    fun z => LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e) z

/-! ### The dimensions along a residue class are eventually constant -/

/-- **Along an arithmetic progression of twist degrees going down, the dimensions of `H¹` are
non-increasing, hence eventually constant.**  One step down is an injection, by hypothesis. -/
theorem exists_forall_eq_finrank_cohomologyOverField_twistPow (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (F : X.Modules) [F.IsCoherent] {e : ℕ} (he : 1 ≤ e)
    (s : Stacks.Divisors.powSection L (e : ℤ)) (j₀ m : ℤ) (hm : m ≤ j₀)
    (hinj : ∀ j : ℤ, j ≤ j₀ → Function.Injective
      (AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Divisors.actionPow L F (e : ℤ) j s) 1)) :
    ∃ J N : ℕ, ∀ i : ℕ, J ≤ i →
      Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F (m - (i : ℤ) * (e : ℤ))) 1) = N := by
  have hfd := AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f
  refine Stacks.LinearAlgebra.exists_forall_eq_of_antitone
    (fun i => Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F (m - (i : ℤ) * (e : ℤ))) 1)) fun i => ?_
  have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hdeg : (e : ℤ) + (m - ((i : ℤ) + 1) * (e : ℤ)) = m - (i : ℤ) * (e : ℤ) := by ring
  have hj : m - ((i : ℤ) + 1) * (e : ℤ) ≤ j₀ := by nlinarith [Int.natCast_nonneg i]
  have := hfd (Stacks.Divisors.twistPow L F ((e : ℤ) + (m - ((i : ℤ) + 1) * (e : ℤ))))
    (Stacks.Divisors.isCoherent_twistPow L F _) 1
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F (e : ℤ) (m - ((i : ℤ) + 1) * (e : ℤ)) s) 1).hom)
    (hinj (m - ((i : ℤ) + 1) * (e : ℤ)) hj)
  have hfin : ∀ a b : ℤ, a = b → Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F a) 1) = Module.finrank k
        (AlgebraicGeometry.cohomologyOverField k f (Stacks.Divisors.twistPow L F b) 1) := by
    rintro _ _ rfl
    rfl
  exact (hfin _ _ (by push_cast; ring)).le.trans (hle.trans (hfin _ _ hdeg).le)

/-! ### Propagating the annihilation of `H¹` downwards

Multiplication by two sections commutes
(`Stacks.Cohomology.TwistCohomologyAction.cohomologyOverFieldMap_actionOf_comm`), up to the
reindexing comparisons that bring the two orders of the degrees to a common total degree.  If
multiplication by `s'` kills `H¹` in degree `e + j` and multiplication by the regular section `σ`
is injective in degree `d + j`, then one square says multiplication by `s'` already kills `H¹` in
degree `j`.  Iterating this is what makes the annihilator of the multiplication independent of the
degree, which is the step the source performs with "the diagram commutes with isomorphisms going
vertically". -/

/-- **One step of the downward propagation.** -/
theorem eq_zero_cohomologyOverFieldMap_actionPow_of_add (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) {e : ℕ} (σ : Stacks.Divisors.powSection L (e : ℤ))
    (d : ℤ) (s : Stacks.Divisors.powSection L d) (j : ℤ)
    (hσ : Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F (e : ℤ) (d + j) σ) 1))
    (h : AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F d ((e : ℤ) + j) s) 1 = 0) :
    AlgebraicGeometry.cohomologyOverFieldMap k f (Stacks.Divisors.actionPow L F d j s) 1 = 0 := by
  have h₁ : d + ((e : ℤ) + j) = (e : ℤ) + d + j := by ring
  have h₂ : (e : ℤ) + (d + j) = (e : ℤ) + d + j := by ring
  have hsq := Stacks.Cohomology.TwistCohomologyAction.cohomologyOverFieldMap_actionOf_comm
    k f L F 1 d (e : ℤ) j s σ h₁ h₂
  have hγ : Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Cohomology.TwistedGradedModule.reindexTwist X L F h₂) 1) :=
    injective_cohomologyOverFieldMap_of_inverse k f _
      (Stacks.SheafOfModules.Invertible.tensorProductIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (Iso.refl F)
        (Stacks.SheafOfModules.TensorPower.tensorPowerReindex X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L h₂)).inv
      (Iso.hom_inv_id _) 1
  have hLHS : AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Divisors.actionPow L F (e : ℤ) j σ) 1 ≫
      AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Divisors.actionPow L F d ((e : ℤ) + j) s) 1 ≫
      AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Cohomology.TwistedGradedModule.reindexTwist X L F h₁) 1 = 0 := by
    rw [h, Limits.zero_comp, Limits.comp_zero]
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  refine hσ (hγ ?_)
  have hz := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (hsq.symm.trans hLHS)) z
  simpa using hz

/-- **The downward propagation, iterated.**  If multiplication by `s` kills `H¹` in degree `j₁`
and multiplication by the regular section `σ` is injective in every degree at most `d + j₁`, then
multiplication by `s` kills `H¹` in every degree `j₁ - a e`. -/
theorem eq_zero_cohomologyOverFieldMap_actionPow_sub (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) {e : ℕ} (he : 1 ≤ e)
    (σ : Stacks.Divisors.powSection L (e : ℤ)) (d : ℤ) (s : Stacks.Divisors.powSection L d)
    (j₁ : ℤ)
    (hσ : ∀ j : ℤ, j ≤ d + j₁ → Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F (e : ℤ) j σ) 1))
    (h : AlgebraicGeometry.cohomologyOverFieldMap k f (Stacks.Divisors.actionPow L F d j₁ s) 1 = 0)
    (a : ℕ) :
    AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F d (j₁ - (a : ℤ) * (e : ℤ)) s) 1 = 0 := by
  have hepos : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hcast : ∀ D D' : ℤ, D = D' → AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F d D s) 1 = 0 → AlgebraicGeometry.cohomologyOverFieldMap k f
        (Stacks.Divisors.actionPow L F d D' s) 1 = 0 := by
    rintro _ _ rfl
    exact id
  induction a with
  | zero => exact hcast _ _ (by ring) h
  | succ a ih =>
      have hd : (e : ℤ) + (j₁ - ((a : ℤ) + 1) * (e : ℤ)) = j₁ - (a : ℤ) * (e : ℤ) := by ring
      have hstep : AlgebraicGeometry.cohomologyOverFieldMap k f
          (Stacks.Divisors.actionPow L F d ((e : ℤ) + (j₁ - ((a : ℤ) + 1) * (e : ℤ))) s) 1 = 0 :=
        hcast _ _ hd.symm ih
      have hle : d + (j₁ - ((a : ℤ) + 1) * (e : ℤ)) ≤ d + j₁ := by
        nlinarith [Int.natCast_nonneg a]
      refine hcast (j₁ - ((a : ℤ) + 1) * (e : ℤ)) _ (by push_cast; ring) ?_
      exact eq_zero_cohomologyOverFieldMap_actionPow_of_add L k f F σ d s
        (j₁ - ((a : ℤ) + 1) * (e : ℤ)) (hσ _ hle) hstep

/-! ### From one residue class to all sufficiently negative degrees -/

/-- **Vanishing along every arithmetic progression of modulus `e` gives vanishing in all
sufficiently negative degrees.** -/
theorem exists_forall_le_isZero_of_forall_residue_start (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (F : X.Modules) {e : ℕ} (he : 1 ≤ e)
    (hstart : ∀ m : ℤ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      IsZero (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F (m - (j : ℤ) * (e : ℤ))) 1)) :
    ∃ m₀ : ℤ, ∀ m : ℤ, m ≤ m₀ →
      IsZero (AlgebraicGeometry.cohomologyOverField k f (Stacks.Divisors.twistPow L F m) 1) := by
  choose J hJ using fun i : ℕ => hstart (-(i : ℤ))
  exact exists_forall_le_of_forall_residue he
    (fun n => IsZero (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F n) 1)) J fun i _ j hij => hJ i j hij

/-! ### The core contradiction

A section `s` of `ℒ^{⊗ d}` which annihilates `H¹` in one degree annihilates it in every degree
further down the progression; and if `s` vanishes at no associated point of `ℱ`, multiplication
by it is *injective* on `H¹` in all sufficiently negative degrees.  Both at once force `H¹` to
vanish somewhere down the progression. -/

/-- **A regular section annihilating `H¹` in one degree makes `H¹` vanish somewhere down the
progression.** -/
theorem exists_isZero_cohomologyOverField_of_annihilating (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hL : Stacks.Ample.IsAmple X L) (F : X.Modules)
    [F.IsCoherent]
    (hdepth : ∀ y : X, IsClosed ({y} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y))
    {e : ℕ} (he : 1 ≤ e) (σ : Stacks.Divisors.powSection L (e : ℤ)) (j₀ : ℤ)
    (hinj : ∀ j : ℤ, j ≤ j₀ → Function.Injective (AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F (e : ℤ) j σ) 1))
    (d : ℤ) (s : Stacks.Divisors.powSection L d)
    (hs : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L d)
        (AlgebraicGeometry.restrictTerminalTopEquiv _ s))
    (j₁ : ℤ) (hj₁ : d + j₁ ≤ j₀)
    (hann : AlgebraicGeometry.cohomologyOverFieldMap k f
      (Stacks.Divisors.actionPow L F d j₁ s) 1 = 0) :
    ∃ a : ℕ, IsZero (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F (j₁ - (a : ℤ) * (e : ℤ))) 1) := by
  obtain ⟨j₂, hj₂⟩ :=
    exists_forall_le_injective_cohomologyOverFieldMap_actionPow L k f hL F d s hs hdepth
  have hepos : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he
  refine ⟨(j₁ - j₂).toNat, ?_⟩
  have hdeg : j₁ - ((j₁ - j₂).toNat : ℤ) * (e : ℤ) ≤ j₂ := by
    nlinarith [Int.self_le_toNat (j₁ - j₂), Int.natCast_nonneg (j₁ - j₂).toNat]
  have hzero := eq_zero_cohomologyOverFieldMap_actionPow_sub L k f F he σ d s j₁
    (fun j hj => hinj j (le_trans hj hj₁)) hann (j₁ - j₂).toNat
  have hinj2 := hj₂ _ hdeg
  have hsub : Subsingleton (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F (j₁ - ((j₁ - j₂).toNat : ℤ) * (e : ℤ))) 1) := by
    refine ⟨fun a b => hinj2 ?_⟩
    have h0 := congrArg ModuleCat.Hom.hom hzero
    simp only [ModuleCat.hom_zero] at h0
    exact (LinearMap.congr_fun h0 a).trans (LinearMap.congr_fun h0 b).symm
  exact _root_.ModuleCat.isZero_of_subsingleton _

/-! ### The `k`-linear pairing and the codimension of its kernel

`Stacks.Cohomology.TwistCohomologyAction.twistCohomologyAction` is already the `k`-linear map
`Γ(X, ℒ^{⊗ d}) →ₗ[k] (H¹(ℱ(j)) →ₗ[k] H¹(ℱ(d + j)))`; composing it with
`Stacks.EnriquesSeveriZariski.twistSectionSpaceEquiv` puts its source at the spelling of the
space of sections that the codimension count uses.  The kernel then has codimension at most the
product of the two dimensions, by linear algebra alone. -/

/-- **Multiplication on `H¹`, as a `k`-linear map in the multiplying section.** -/
def h1Pairing (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (F : X.Modules) (d j : ℤ) :
    AlgebraicGeometry.globalSectionsOverField k f
        (Stacks.Algebraization.tensorPowScheme X L d) →ₗ[k]
      (AlgebraicGeometry.cohomologyOverField k f (Stacks.Divisors.twistPow L F j) 1 →ₗ[k]
        AlgebraicGeometry.cohomologyOverField k f (Stacks.Divisors.twistPow L F (d + j)) 1) :=
  (Stacks.Cohomology.TwistCohomologyAction.twistCohomologyAction k f L F 1 d j).comp
    (twistSectionSpaceEquiv L k f d).symm.toLinearMap

/-- The pairing is multiplication by the section, read on cohomology. -/
theorem h1Pairing_apply (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (F : X.Modules) (d j : ℤ)
    (v : AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)) :
    h1Pairing L k f F d j v =
      (AlgebraicGeometry.cohomologyOverFieldMap k f (Stacks.Divisors.actionPow L F d j
        ((AlgebraicGeometry.restrictTerminalTopEquiv
          (Stacks.Algebraization.tensorPowScheme X L d)).symm v)) 1).hom := rfl

/-- **The sections annihilating `H¹` in one degree form a subspace of codimension at most the
product of the two dimensions.** -/
theorem finrank_quotient_ker_h1Pairing_le (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (F : X.Modules) [F.IsCoherent] (d j : ℤ) :
    Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
          (Stacks.Algebraization.tensorPowScheme X L d) ⧸
        LinearMap.ker (h1Pairing L k f F d j)) ≤
      Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
          (Stacks.Divisors.twistPow L F j) 1) *
        Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
          (Stacks.Divisors.twistPow L F (d + j)) 1) := by
  have hfd := AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper k f
  have := hfd (Stacks.Divisors.twistPow L F j) (Stacks.Divisors.isCoherent_twistPow L F j) 1
  have := hfd (Stacks.Divisors.twistPow L F (d + j))
    (Stacks.Divisors.isCoherent_twistPow L F (d + j)) 1
  exact Stacks.LinearAlgebra.finrank_quotient_ker_le k _ _ _ (h1Pairing L k f F d j)

/-! ### The selection step

Inside the annihilator of the pairing — a subspace of codimension at most `N²` — one has to find
a section vanishing at no associated point of `ℱ`.  `Stacks.LinearAlgebra.exists_notMem_biUnion`
does that uniformly in the field, provided each of the finitely many subspaces to be avoided has
codimension at least the number of them; intersecting with the annihilator costs at most `N²`
more, which is why the codimension asked for below is `t.card + N²`. -/

/-- **A section annihilating `H¹` in one degree and vanishing at no associated point of `ℱ` can
be selected**, provided the sections vanishing at each associated point have codimension at least
`t.card + N²`. -/
theorem exists_annihilating_regular_section (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsProper f] (F : X.Modules) [F.IsCoherent] (d j : ℤ) (t : Finset X)
    (W : X → Submodule k (AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)))
    (hW : ∀ x ∈ t, t.card +
      Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F j) 1) *
      Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
        (Stacks.Divisors.twistPow L F (d + j)) 1) +
      Module.finrank k (W x) ≤ Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
        (Stacks.Algebraization.tensorPowScheme X L d))) :
    ∃ v : AlgebraicGeometry.globalSectionsOverField k f
        (Stacks.Algebraization.tensorPowScheme X L d),
      h1Pairing L k f F d j v = 0 ∧ ∀ x ∈ t, v ∉ W x := by
  classical
  have : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : Stacks.Ample.IsInvertibleModule X (Stacks.Algebraization.tensorPowScheme X L d) :=
    Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L d
  have : (Stacks.Algebraization.tensorPowScheme X L d).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  have : FiniteDimensional k (AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)) :=
    AlgebraicGeometry.finiteDimensional_globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d)
  set NN := Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F j) 1) *
    Module.finrank k (AlgebraicGeometry.cohomologyOverField k f
      (Stacks.Divisors.twistPow L F (d + j)) 1) with hNN
  set V := LinearMap.ker (h1Pairing L k f F d j) with hV
  have hquot : Module.finrank k (AlgebraicGeometry.globalSectionsOverField k f
      (Stacks.Algebraization.tensorPowScheme X L d) ⧸ V) ≤ NN :=
    finrank_quotient_ker_h1Pairing_le L k f F d j
  have hsplit := Submodule.finrank_quotient_add_finrank V
  obtain ⟨w, hw⟩ := Stacks.LinearAlgebra.exists_notMem_biUnion k V t
    (fun x => (W x).comap V.subtype) fun x hx => by
      have h1 : Module.finrank k ((W x).comap V.subtype) ≤ Module.finrank k (W x) :=
        calc Module.finrank k ((W x).comap V.subtype)
            = Module.finrank k (((W x).comap V.subtype).map V.subtype) :=
              (V.equivSubtypeMap ((W x).comap V.subtype)).finrank_eq
          _ = Module.finrank k (V ⊓ W x : Submodule k _) := by
              rw [Submodule.map_comap_subtype]
          _ ≤ Module.finrank k (W x) := Submodule.finrank_mono inf_le_right
      have h2 := hW x hx
      omega
  exact ⟨V.subtype w, w.2, fun x hx hmem => hw x hx hmem⟩

end Stacks.EnriquesSeveriZariski

end
