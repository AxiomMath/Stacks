module

public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.FromAmple
public import StacksFrontier.AlgebraicGeometry.AmplePullbackCovering.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.FunctionFieldDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Reduction
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Map
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.RingTheory.Nagata.Japanese
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Norm

/-!
# Descent of an ample invertible module along a norm

Let `f : X ⟶ Y` be a finite morphism of schemes carrying a norm on functions, and let `L` be an
ample invertible `𝒪_X`-module. Then `Y` carries an ample invertible `𝒪_Y`-module, namely the norm
of a sufficiently high tensor power of `L`.

The argument is the source's. The target is quasi-compact because it is the image of a
quasi-compact scheme under a surjection. For a point `y` of `Y`, choose an affine open `V ∋ y`
and, by [Stacks, Tag 09NV], a global section `s` of `L ^⊗ n` with
`f⁻¹{y} ⊆ X_s ⊆ f⁻¹V`. The norm of `s` is a global section of `Norm(L ^⊗ n)` which does not
vanish at `y` and whose nonvanishing locus lies in `V`, hence is affine by [Stacks, Tag 01PV].
Those nonvanishing loci cover `Y`, so finitely many suffice, and raising their sections to a
common multiple of their degrees puts them all in one module `Norm(L ^⊗ D)`, which is therefore
ample with no tensor power of its own needed.

## The common degree, and why it is needed

The source writes `Norm(s)` as "a section of `Norm(L) ^⊗ n`", which is the Picard-group clause of
[Stacks, Tag 0BCY] — the statement that the norm construction is additive on isomorphism classes.
That clause is not used here (`Stacks.Divisors.normInvertibleData` constructs the object and its
action on local generators, not the Picard map), and it is not needed: ampleness asks
for *some* positive power, so after shrinking to a finite subcover one may raise every section to
one common degree `D` and read all the resulting sections in the single module `Norm(L ^⊗ D)` at
exponent one. Raising a section is
`Stacks.Ample.exists_tensorPow_nonvanishingLocus_eq_of_dvd`, a power in the graded ring of
sections, whose nonvanishing locus is that of the section itself.

## Main definitions

* `Stacks.SheafOfModules.unitHom` and `Stacks.SheafOfModules.ofUnitHom`: the bijection between
  global sections of a module and maps out of the structure sheaf.
* `Stacks.SheafOfModules.unitGenerator` and `Stacks.SheafOfModules.generatorOfTrivialization`:
  the local frames supplied by the section `1` of `𝒪_X` and by a sectionwise trivialization.
* `Stacks.Divisors.normGlobalSection`: the norm of a global section of an invertible module.

## Main results

* `Stacks.SheafOfModules.zeroAt_unitHom_iff_notMem_nonvanishingLocus`: **the comparison of the
  two notions of vanishing** — the frame-wise `Stacks.SheafOfModules.zeroAt` of
  [Stacks, Tag 0BCZ] and the nonvanishing locus of [Stacks, Tag 01CY] — for a global section of
  an invertible module.
* `Stacks.Divisors.mem_nonvanishingLocus_normGlobalSection_iff`: the norm of a section is
  nonvanishing at `y` exactly when the section is nonvanishing on the whole fibre over `y`.
* `Stacks.Divisors.isAffineOpen_nonvanishingOpen_normGlobalSection`: [Stacks, Tag 01PV] applied
  to that locus.
* `Stacks.Ample.exists_tensorPow_nonvanishingLocus_eq_of_dvd`: a section of a positive tensor
  power can be replaced, with the same nonvanishing locus, by one of any positive multiple of
  its degree.
* `Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus`: a module with enough global
  sections of affine nonvanishing locus is ample, with no tensor power needed.
* `Stacks.Divisors.exists_isAmple_of_morphismNormMap`: **the content of Tag 0BD0**, for a finite
  surjective morphism and a norm map of no particular degree.
* `Stacks.Divisors.exists_isAmple_of_hasNormOfDegree`: **Stacks Tag 0BD0.**
* `Stacks.Divisors.exists_isAmple_of_isFiniteLocallyFree`,
  `Stacks.Divisors.exists_isAmple_of_isIntegral_isNormal` and
  `Stacks.Divisors.exists_isAmple_of_isAmple_reduction_char_p`: **the three cases of Stacks
  Tag 0BD4.**

## Implementation notes

**Which ampleness.** `Stacks.Ample.IsAmple`, over the integer tensor powers
`Stacks.Ample.tensorPowModule`. The ample results used here — Tag 09NV, Tag 01PV's consumers, the
graded avoidance — are stated with this predicate, and `Stacks.Ample.isAmple_iff_isAmpleForPowers`
proves it does not depend on which construction of the powers is used.

**Which invertibility.** `Stacks.Ample.IsInvertibleModule`, i.e.
`AlgebraicGeometry.SheafOfModules.IsInvertible`, the class the ample development and the norm
construction are both stated in. `Stacks.Divisors.isInvertible_normInvertible` concludes in the
other Tag 01CS class, `Stacks.SheafOfModules.IsInvertible`, and
`Stacks.Divisors.isInvertibleModule_normInvertible` carries it across once, as an instance, by
`Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible`.

**No degree.** `Stacks.Divisors.exists_isAmple_of_morphismNormMap` asks only for a
`Stacks.Norm.MorphismNormMap` — multiplicativity, naturality and the vanishing axiom — and
for surjectivity. That is all the norm construction of Tag 0BCY and the norm map of Tag 0BCZ use;
the degree enters Tag 0BD0 only through
`Stacks.Divisors.surjective_of_hasNormOfDegree`. Case (1) of Tag 0BD4 is what forces the
distinction: there the morphism is surjective by hypothesis and the canonical determinant norm of
Tag 0BD2 exists at *varying* rank, so no constant degree is available, and gluing the strata's
degrees into one is unnecessary.

## References

* [Stacks Project, Tag 0BD0](https://stacks.math.columbia.edu/tag/0BD0)
* [Stacks Project, Tag 0BD4](https://stacks.math.columbia.edu/tag/0BD4)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BCZ](https://stacks.math.columbia.edu/tag/0BCZ)
* [Stacks Project, Tag 09NV](https://stacks.math.columbia.edu/tag/09NV)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Ample
open Stacks.SheafOfModules (GeneratorSections)

universe u

namespace Stacks.SheafOfModules

variable {X : Scheme.{u}}

/-- The section `1` of the structure sheaf generates it on every open. -/
noncomputable def unitGenerator (X : Scheme.{u}) (U : X.Opens) :
    GeneratorSections X.toRingedSpace (unitModule X) U :=
  generatorOfIso (X := X.toRingedSpace) (unitModule X) (Iso.refl _)

/-- The generating section of the structure sheaf is `1`. -/
@[simp] theorem unitGenerator_val (X : Scheme.{u}) (U : X.Opens) :
    (unitGenerator X U).val = (1 : Γ(X, U)) := rfl

/-- The basis section of a sectionwise trivialization generates the module on the trivializing
open. -/
noncomputable def generatorOfTrivialization {M : X.Modules} {V : X.Opens}
    (τ : Stacks.SheafDescent.Trivialization X.presheaf M.val V) :
    GeneratorSections X.toRingedSpace M V := by
  refine ⟨Stacks.NonvanishingOpen.basis τ, fun W h => ?_⟩
  change Function.Bijective
    (fun r : Γ(X, W) => r • M.presheaf.map (homOfLE h).op (Stacks.NonvanishingOpen.basis τ))
  have hleft (r : Γ(X, W)) :
      Stacks.NonvanishingOpen.triv τ (homOfLE h)
        (r • M.presheaf.map (homOfLE h).op (Stacks.NonvanishingOpen.basis τ)) = r := by
    rw [Stacks.NonvanishingOpen.triv_smul, Stacks.NonvanishingOpen.triv_res_basis, mul_one]
  exact ⟨Function.LeftInverse.injective hleft, fun u ↦
    ⟨Stacks.NonvanishingOpen.triv τ (homOfLE h) u,
      (Stacks.SectionProduct.eq_triv_smul_res_basis τ (homOfLE h) u).symm⟩⟩

/-- A global section of an `𝒪_X`-module, read as a map out of the structure sheaf. -/
@[ega "II 6.5.3" "partial"]
noncomputable def unitHom (M : X.Modules) (s : Γ(M, ⊤)) : unitModule X ⟶ M :=
  M.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm s)

/-- The map out of the structure sheaf named by a global section sends `1` over an open to the
restriction of that section. -/
theorem unitHom_app_one (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens) :
    (unitHom M s).val.app (op U) (1 : Γ(X, U)) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s := by
  have h : (M.unitHomEquiv (unitHom M s)).val (op U) =
      (unitHom M s).val.app (op U) (1 : Γ(X, U)) :=
    SheafOfModules.unitHomEquiv_apply_coe M (unitHom M s) (op U)
  rw [show M.unitHomEquiv (unitHom M s) =
      (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm s from
    M.unitHomEquiv.apply_symm_apply _] at h
  exact h.symm

/-- **A global section of an invertible module vanishes at a point, in the sense of the frame
calculus of [Stacks, Tag 0BCZ], exactly when the point is outside its nonvanishing locus of
[Stacks, Tag 01CY].** -/
theorem zeroAt_unitHom_iff_notMem_nonvanishingLocus (M : X.Modules)
    [IsInvertibleModule X M] (s : Γ(M, ⊤)) (x : X) :
    zeroAt (unitModule X) M (unitHom M s) x ↔ x ∉ Stacks.Ample.nonvanishingLocus M s := by
  obtain ⟨V, hxV, ⟨τ⟩⟩ := Stacks.SectionProduct.exists_trivialization_at M x
  have hcoeff : (unitHom M s).val.app (op V) (unitGenerator X V).val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op V)) (M.val.obj (op V)) _
        (Stacks.NonvanishingOpen.trivTop τ s) (generatorOfTrivialization τ).val := by
    rw [unitGenerator_val, unitHom_app_one]
    exact Stacks.NonvanishingOpen.eq_triv_smul_basis τ _
  rw [zeroAt_iff_evaluation_eq_zero (unitModule X) M (unitHom M s) V x hxV
      (unitGenerator X V) (generatorOfTrivialization τ) _ hcoeff,
    Scheme.evaluation_eq_zero_iff_notMem_basicOpen,
    Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit τ s hxV]
  exact not_congr (X.mem_basicOpen _ x hxV)

/-- The global section named by a map out of the structure sheaf; inverse to
`Stacks.SheafOfModules.unitHom`. -/
@[ega "II 6.5.3" "partial"]
noncomputable def ofUnitHom (M : X.Modules) (φ : unitModule X ⟶ M) : Γ(M, ⊤) :=
  Stacks.NonvanishingSpelling.sectionsEquiv X M (M.unitHomEquiv φ)

/-- **The two readings of a global section agree**: a map out of the structure sheaf is recovered
from the global section it names. -/
@[simp,
  ega "0 5.1.1" "partial",
  ega "II 6.5.3" "partial"]
theorem unitHom_ofUnitHom (M : X.Modules) (φ : unitModule X ⟶ M) :
    unitHom M (ofUnitHom M φ) = φ := by
  change M.unitHomEquiv.symm
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm
      (Stacks.NonvanishingSpelling.sectionsEquiv X M (M.unitHomEquiv φ))) = φ
  rw [Equiv.symm_apply_apply]
  exact M.unitHomEquiv.symm_apply_apply φ

/-- **Precomposing a map of modules with a global generator does not move its vanishing
locus.** -/
theorem zeroAt_comp_unitHom_iff {M N : X.Modules} [IsInvertibleModule X N]
    (g : GeneratorSections X.toRingedSpace M ⊤) (ψ : M ⟶ N) (x : X) :
    zeroAt (unitModule X) N (unitHom M g.val ≫ ψ) x ↔ zeroAt M N ψ x := by
  obtain ⟨V, hxV, ⟨τ⟩⟩ := Stacks.SectionProduct.exists_trivialization_at N x
  set t := generatorOfTrivialization τ with ht
  set m := generatorRestrict (X := X.toRingedSpace) M (le_top : V ≤ ⊤) g with hm
  set a := generatorCoefficient (X := X.toRingedSpace) M N ψ V m t with ha
  have hspec : ψ.val.app (op V) m.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op V)) (N.val.obj (op V)) _ a t.val :=
    generatorCoefficient_spec (X := X.toRingedSpace) M N ψ V m t
  have hcomp : (unitHom M g.val ≫ ψ).val.app (op V) (unitGenerator X V).val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op V)) (N.val.obj (op V)) _ a t.val := by
    refine Eq.trans ?_ hspec
    have h1 : (unitHom M g.val).val.app (op V) (1 : Γ(X, V)) = m.val :=
      unitHom_app_one M g.val V
    change ψ.val.app (op V) ((unitHom M g.val).val.app (op V) (1 : Γ(X, V))) = _
    exact congrArg (fun z => ψ.val.app (op V) z) h1
  rw [zeroAt_iff_evaluation_eq_zero (unitModule X) N _ V x hxV (unitGenerator X V) t a hcomp,
    zeroAt_iff_generatorCoefficient_eq_zero M N ψ V x hxV m t]

end Stacks.SheafOfModules

namespace Stacks.Divisors

open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (N : MorphismNormMap f)

/-- The norm of an invertible module is invertible. -/
@[ega "II 6.5.2" "partial"]
instance isInvertibleModule_normInvertible (A : X.Modules) [IsInvertibleModule X A] :
    IsInvertibleModule Y (normInvertible f N A) :=
  haveI := isInvertible_normInvertible f N A (hasTrivializingTargetCover_of_isInvertible f A)
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **The norm of the structure sheaf is trivial**: the norm of the generator `1` of `𝒪_X`
generates `Norm(𝒪_X)` on all of `Y`. -/
@[ega "II 6.5.2"]
noncomputable def normUnitGenerator :
    GeneratorSections Y.toRingedSpace (normInvertible f N (unitModule X)) ⊤ :=
  normGenerator f N (unitModule X)
    (hasTrivializingTargetCover_of_isInvertible f (unitModule X)) ⊤
    (unitGenerator X (f ⁻¹ᵁ (⊤ : Y.Opens)))

/-- **The norm of a global section**, as a map out of the structure sheaf of the target: the
norm of the map `𝒪_X ⟶ A` the section names, precomposed with the trivialization of
`Norm(𝒪_X)`. -/
@[ega "II 6.5.5" "more general"]
noncomputable def normSectionHom (A : X.Modules) [IsInvertibleModule X A] (s : Γ(A, ⊤)) :
    unitModule Y ⟶ normInvertible f N A :=
  unitHom (normInvertible f N (unitModule X)) (normUnitGenerator f N).val ≫
    normMapOfCover f N (unitModule X) A
      (hasTrivializingTargetCover_of_isInvertible f (unitModule X))
      (hasTrivializingTargetCover_of_isInvertible f A) (unitHom A s)

/-- **The norm of a global section of an invertible module**, a global section of the norm. -/
noncomputable def normGlobalSection (A : X.Modules) [IsInvertibleModule X A] (s : Γ(A, ⊤)) :
    Γ(normInvertible f N A, ⊤) :=
  ofUnitHom (normInvertible f N A) (normSectionHom f N A s)

/-- **The nonvanishing locus of the norm of a section**: the norm of `s` is nonvanishing at `y`
exactly when `s` is nonvanishing at every point of the fibre over `y`. This is the vanishing
clause of [Stacks, Tag 0BCZ] read on global sections. -/
theorem mem_nonvanishingLocus_normGlobalSection_iff (A : X.Modules) [IsInvertibleModule X A]
    (s : Γ(A, ⊤)) (y : Y) :
    y ∈ Stacks.Ample.nonvanishingLocus (normInvertible f N A) (normGlobalSection f N A s) ↔
      ∀ x : X, f x = y → x ∈ Stacks.Ample.nonvanishingLocus A s := by
  have hbridgeY := zeroAt_unitHom_iff_notMem_nonvanishingLocus (normInvertible f N A)
    (normGlobalSection f N A s) y
  rw [normGlobalSection, unitHom_ofUnitHom] at hbridgeY
  have hcov := hasTrivializingTargetCover_of_isInvertible f (unitModule X)
  have hcomp := zeroAt_comp_unitHom_iff (normUnitGenerator f N)
    (normMapOfCover f N (unitModule X) A hcov
      (hasTrivializingTargetCover_of_isInvertible f A) (unitHom A s)) y
  have hnorm := normMapOfCover_zeroAt_iff f N (unitModule X) A hcov
    (hasTrivializingTargetCover_of_isInvertible f A) (unitHom A s) y
  constructor
  · intro hy x hx
    by_contra hnv
    exact hbridgeY.mp (hcomp.mpr (hnorm.mpr
      ⟨x, hx, (zeroAt_unitHom_iff_notMem_nonvanishingLocus A s x).mpr hnv⟩)) hy
  · intro hall
    by_contra hy
    obtain ⟨x, hx, hzx⟩ := hnorm.mp (hcomp.mp (hbridgeY.mpr hy))
    exact (zeroAt_unitHom_iff_notMem_nonvanishingLocus A s x).mp hzx (hall x hx)

/-- **The nonvanishing open of the norm of a section is contained in any target open whose
inverse image contains the nonvanishing locus of the section.** Surjectivity of `f` is what makes
this work: a point of the target where the norm is nonvanishing is the image of a point where the
section is. -/
theorem nonvanishingOpen_normGlobalSection_le (hsurj : Function.Surjective f.base)
    (A : X.Modules) [IsInvertibleModule X A] (s : Γ(A, ⊤)) {V : Y.Opens}
    (hsub : Stacks.Ample.nonvanishingLocus A s ⊆ (f ⁻¹ᵁ V : Set X)) :
    Stacks.NonvanishingOpen.nonvanishingOpen Y (normInvertible f N A)
        (normGlobalSection f N A s) ≤ V := by
  intro z hz
  obtain ⟨x, hx⟩ := hsurj z
  have hxs : x ∈ Stacks.Ample.nonvanishingLocus A s :=
    (mem_nonvanishingLocus_normGlobalSection_iff f N A s z).mp hz x hx
  exact hx ▸ hsub hxs

/-- **[Stacks, Tag 01PV] applied to the norm of a section**: when the nonvanishing locus of `s`
lies over an affine open `V` of the target, the nonvanishing locus of its norm is affine, being
contained in `V`. -/
theorem isAffineOpen_nonvanishingOpen_normGlobalSection (hsurj : Function.Surjective f.base)
    (A : X.Modules) [IsInvertibleModule X A] (s : Γ(A, ⊤)) {V : Y.Opens}
    (hVaff : IsAffineOpen V)
    (hsub : Stacks.Ample.nonvanishingLocus A s ⊆ (f ⁻¹ᵁ V : Set X)) :
    IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen Y (normInvertible f N A)
      (normGlobalSection f N A s)) := by
  have hle := nonvanishingOpen_normGlobalSection_le f N hsurj A s hsub
  have hcap := Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (normInvertible f N A) (normGlobalSection f N A s) hVaff
  rwa [inf_eq_right.mpr hle] at hcap

end Stacks.Divisors

namespace Stacks.Ample

variable {X : Scheme.{u}}

/-- **A global section of a positive tensor power can be replaced, with the same nonvanishing
locus, by a section of any positive multiple of its degree.** The replacement is a power of the
section in the graded ring of sections, whose nonvanishing locus is that of the section itself. -/
theorem exists_tensorPow_nonvanishingLocus_eq_of_mul (L : X.Modules) [IsInvertibleModule X L]
    {n : ℕ} (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) {k : ℕ} (hk : 1 ≤ k) :
    ∃ s' : Γ(tensorPowModule X L ((n * k : ℕ) : ℤ), ⊤),
      nonvanishingLocus (tensorPowModule X L ((n * k : ℕ) : ℤ)) s' =
        nonvanishingLocus (tensorPowModule X L (n : ℤ)) s := by
  obtain ⟨a, ha⟩ := Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L n s
  obtain ⟨s', hs'⟩ := Stacks.AmpleFiniteAffineNonvanishing.exists_tensorPow_powNonvanishingOpen_eq L
    (Stacks.SectionExtension.powSec L a k)
  refine ⟨s', ?_⟩
  calc nonvanishingLocus (tensorPowModule X L ((n * k : ℕ) : ℤ)) s'
      = (Stacks.AmpleTheory.powNonvanishingOpen X L (n * k) s' : Set X) := rfl
    _ = (Stacks.AmpleFiniteAvoidance.nvOpen L (Stacks.SectionExtension.powSec L a k) : Set X) :=
        congrArg (fun U : X.Opens => (U : Set X)) hs'
    _ = Stacks.AmpleFiniteAvoidance.nvLocus L (Stacks.SectionExtension.powSec L a k) :=
        Stacks.AmpleFiniteAvoidance.coe_nvOpen L _
    _ = Stacks.AmpleFiniteAvoidance.nvLocus L a :=
        Stacks.SectionExtension.nvLocus_powSec_of_one_le L a k hk
    _ = nonvanishingLocus (tensorPowModule X L (n : ℤ)) s := ha

/-- **A global section of a positive tensor power can be replaced, with the same nonvanishing
locus, by a section of any positive multiple of its degree.** -/
theorem exists_tensorPow_nonvanishingLocus_eq_of_dvd (L : X.Modules) [IsInvertibleModule X L]
    {n D : ℕ} (hD : 0 < D) (hdvd : n ∣ D) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    ∃ s' : Γ(tensorPowModule X L (D : ℤ), ⊤),
      nonvanishingLocus (tensorPowModule X L (D : ℤ)) s' =
        nonvanishingLocus (tensorPowModule X L (n : ℤ)) s := by
  obtain ⟨k, rfl⟩ := hdvd
  exact exists_tensorPow_nonvanishingLocus_eq_of_mul L s
    (Nat.one_le_iff_ne_zero.mpr fun h => by simp [h] at hD)

/-- **A module with enough global sections of affine nonvanishing locus is ample**, with no
tensor power needed: the first power suffices. -/
theorem isAmple_of_forall_exists_affine_nonvanishingLocus [CompactSpace X] (M : X.Modules)
    [IsInvertibleModule X M]
    (h : ∀ x : X, ∃ s : Γ(M, ⊤), x ∈ nonvanishingLocus M s ∧
      IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen X M s)) :
    IsAmple X M := by
  refine ⟨inferInstance, fun x => ⟨1, le_rfl, ?_⟩⟩
  obtain ⟨s, hxs, haff⟩ := h x
  have hdeg : ((1 : ℕ) : ℤ) = 1 := Nat.cast_one
  let e : M ≅ tensorPowModule X M ((1 : ℕ) : ℤ) :=
    (tensorPowModuleOneIso X M).symm ≪≫
      eqToIso (congrArg (tensorPowModule X M) hdeg.symm)
  refine ⟨e.hom.app ⊤ s, Stacks.NonvanishingOpen.nonvanishingOpen X M s, ?_, hxs, haff⟩
  rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen]
  exact (nonvanishingLocus_congr e s).symm

end Stacks.Ample

namespace Stacks.Divisors
open Stacks.Norm (MorphismNormMap MorphismNorm HasNormOfDegree IsDeterminantNorm)

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}}

/-- **The content of [Stacks, Tag 0BD0].** A finite *surjective* morphism carrying a norm map on
functions descends the existence of an ample invertible module: the norm of a sufficiently high
tensor power of the given one is ample.

No degree is needed. The degree enters Tag 0BD0 only to force surjectivity
(`Stacks.Divisors.surjective_of_hasNormOfDegree`), and the norm construction of
[Stacks, Tag 0BCY] and its action on maps of [Stacks, Tag 0BCZ] use only multiplicativity,
naturality and the vanishing axiom — the three fields of
`Stacks.Norm.MorphismNormMap`. Stating the step this way is what makes case (1) of
[Stacks, Tag 0BD4] available, where the morphism is surjective by hypothesis and the canonical
determinant norm has no constant degree. -/
theorem exists_isAmple_of_morphismNormMap (f : X ⟶ Y) [IsFinite f] (N : MorphismNormMap f)
    (hsurj : Function.Surjective f.base) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    ∃ (M : Y.Modules) (hM : IsInvertibleModule Y M), @Stacks.Ample.IsAmple Y M hM := by
  classical
  have : CompactSpace X := hL.1
  have : CompactSpace Y := by
    rw [← isCompact_univ_iff, ← Set.range_eq_univ.mpr hsurj, ← Set.image_univ]
    exact isCompact_univ.image f.continuous
  -- One degree, one section and one affine target open for each point of `Y`.
  have hdata : ∀ y : Y, ∃ (n : ℕ) (V : Y.Opens) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)),
      1 ≤ n ∧ IsAffineOpen V ∧
        (∀ x : X, f.base x = y →
          x ∈ Stacks.Ample.nonvanishingLocus (tensorPowModule X L (n : ℤ)) s) ∧
        Stacks.Ample.nonvanishingLocus (tensorPowModule X L (n : ℤ)) s ⊆
          (f ⁻¹ᵁ V : Set X) := by
    intro y
    obtain ⟨R, j, hj, hyj, -⟩ :=
      Y.exists_affine_mem_range_and_range_subset (x := y) (U := ⊤) trivial
    have : IsOpenImmersion j := hj
    have hVaff : IsAffineOpen (j ''ᵁ (⊤ : (Spec R).Opens)) :=
      IsAffineOpen.image_of_isOpenImmersion (isAffineOpen_top _) j
    have hyV : y ∈ j ''ᵁ (⊤ : (Spec R).Opens) := by simpa [Set.image_univ] using hyj
    obtain ⟨n, hn, s, -, hfib, hsmall⟩ :=
      Stacks.AmpleFiniteAffineNonvanishing.exists_affine_nonvanishingOpen_containing_finite L hL
        (f.finite_preimage_singleton y) (f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens)))
        (fun x hx => by
          change f.base x ∈ j ''ᵁ (⊤ : (Spec R).Opens)
          rw [show f.base x = y from hx]
          exact hyV)
    exact ⟨n, j ''ᵁ (⊤ : (Spec R).Opens), s, hn, hVaff,
      fun x hx => hfib (show x ∈ f.base ⁻¹' ({y} : Set Y) from hx), hsmall⟩
  choose n V s hn hVaff hfib hsub using hdata
  -- The nonvanishing opens of the norms of those sections cover `Y`.
  set U : Y → Y.Opens := fun y => Stacks.NonvanishingOpen.nonvanishingOpen Y
    (normInvertible f N (tensorPowModule X L (n y : ℤ)))
    (normGlobalSection f N (tensorPowModule X L (n y : ℤ)) (s y)) with hU
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y : Y => (U y : Set Y))
    (fun y => (U y).2) fun z _ =>
      Set.mem_iUnion.mpr ⟨z, (mem_nonvanishingLocus_normGlobalSection_iff f N _ (s z) z).mpr
        (hfib z)⟩
  -- One common degree for the finitely many sections that are needed.
  have hDpos : 0 < ∏ y ∈ T, n y := Finset.prod_pos fun y _ => hn y
  refine ⟨normInvertible f N (tensorPowModule X L ((∏ y ∈ T, n y : ℕ) : ℤ)), inferInstance, ?_⟩
  refine Stacks.Ample.isAmple_of_forall_exists_affine_nonvanishingLocus _ fun z => ?_
  obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ z))
  obtain ⟨s', hs'⟩ := Stacks.Ample.exists_tensorPow_nonvanishingLocus_eq_of_dvd L hDpos
    (Finset.dvd_prod_of_mem n hyT) (s y)
  have hfibz : ∀ x : X, f x = z →
      x ∈ Stacks.Ample.nonvanishingLocus
        (tensorPowModule X L ((∏ y ∈ T, n y : ℕ) : ℤ)) s' := by
    intro x hx
    rw [hs']
    exact (mem_nonvanishingLocus_normGlobalSection_iff f N _ (s y) z).mp hzy x hx
  have hsubz : Stacks.Ample.nonvanishingLocus
      (tensorPowModule X L ((∏ y ∈ T, n y : ℕ) : ℤ)) s' ⊆ (f ⁻¹ᵁ V y : Set X) := by
    rw [hs']; exact hsub y
  exact ⟨normGlobalSection f N _ s',
    (mem_nonvanishingLocus_normGlobalSection_iff f N _ s' z).mpr hfibz,
    isAffineOpen_nonvanishingOpen_normGlobalSection f N hsurj _ s' (hVaff y) hsubz⟩

/-- **Stacks Project, Tag 0BD0.** Let `f : X ⟶ Y` be a finite morphism of schemes carrying a
norm of positive degree. If `X` has an ample invertible `𝒪_X`-module then so does `Y`: the norm
of a sufficiently high tensor power of the given one.

Positivity of the degree is used exactly once, to see that `f` is surjective; the rest is
`Stacks.Divisors.exists_isAmple_of_morphismNormMap`. -/
@[stacks 0BD0]
theorem exists_isAmple_of_hasNormOfDegree (f : X ⟶ Y) [IsFinite f] (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) {d : ℕ} (hd : 0 < d)
    (hN : HasNormOfDegree f d) :
    ∃ (M : Y.Modules) (hM : IsInvertibleModule Y M), @Stacks.Ample.IsAmple Y M hM := by
  obtain ⟨N⟩ := hN
  exact exists_isAmple_of_morphismNormMap f N.toMorphismNormMap
    (surjective_of_hasNormOfDegree f hd N).1 L hL

/-- **Stacks Project, Tag 0BD4, case (1).** A finite locally free, finite surjective morphism
descends the existence of an ample invertible module. The canonical determinant norm of
[Stacks, Tag 0BD2] is available at *varying* rank, and no constant degree is needed: the degree
is what Tag 0BD0 uses to get surjectivity, and here surjectivity is a hypothesis. -/
@[stacks 0BD4 "finite_locally_free_case",
  ega "II 6.6.1" "absolute, loc free case",
  ega "II 6.6.2" "locally free case"]
theorem exists_isAmple_of_isFiniteLocallyFree (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [Morphisms.IsFiniteLocallyFree f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) :
    ∃ (M : Y.Modules) (hM : IsInvertibleModule Y M), @Stacks.Ample.IsAmple Y M hM :=
  exists_isAmple_of_morphismNormMap f (finiteLocallyFreeNorm f).toMorphismNormMap
    f.surjective L hL

/-- **Stacks Project, Tag 0BD4, case (3).** On a Noetherian scheme of prime characteristic `p`,
an ample invertible module on the reduction descends to an ample invertible module on the scheme:
a Frobenius power supplies a norm of degree a positive power of `p` for the canonical morphism
from the reduction ([Stacks, Tag 0BDZ]). -/
@[stacks 0BD4 "reduction_characteristic_p_case"]
theorem exists_isAmple_of_isAmple_reduction_char_p (Y : Scheme.{u}) [IsNoetherian Y] (p : ℕ)
    (hp : p.Prime) (hchar : (p : Γ(Y, ⊤)) = 0)
    (L : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y)).subscheme.Modules)
    [IsInvertibleModule (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y)).subscheme L]
    (hL : Stacks.Ample.IsAmple
      (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y)).subscheme L) :
    ∃ (M : Y.Modules) (hM : IsInvertibleModule Y M), @Stacks.Ample.IsAmple Y M hM := by
  obtain ⟨e, -, hN⟩ := exists_normOfDegree_reduction Y p hp hchar
  exact exists_isAmple_of_hasNormOfDegree _ L hL (pow_pos hp.pos e) hN

/-- **Stacks Project, Tag 0BD4, case (2).** A finite surjective morphism onto an integral normal
scheme descends the existence of an ample invertible module. The source is replaced by an
irreducible component dominating the target, viewed as a reduced closed subscheme; that component
is integral, so [Stacks, Tag 0BD3] supplies a norm of the function-field degree. -/
@[stacks 0BD4 "integral_normal_case",
  ega "II 6.6.1" "absolute, Y normal",
  ega "II 6.6.2" "Y integral normal"]
theorem exists_isAmple_of_isIntegral_isNormal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] [IsIntegral Y] [IsNormal Y] (L : X.Modules) [IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) :
    ∃ (M : Y.Modules) (hM : IsInvertibleModule Y M), @Stacks.Ample.IsAmple Y M hM := by
  classical
  have hcX : CompactSpace X := hL.1
  obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
  set I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (⟨irreducibleComponent x, isClosed_irreducibleComponent⟩ : Closeds X) with hI
  have hsupport : (I.support : Set X) = irreducibleComponent x := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hxSupport : x ∈ (I.support : Set X) := by
    rw [hsupport]; exact mem_irreducibleComponent
  have hIrr : IsIrreducible (Set.range I.subschemeι.base) := by
    rw [I.range_subschemeι, hsupport]; exact isIrreducible_irreducibleComponent
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I hIrr
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsFinite I.subschemeι := IsFinite.instOfIsClosedImmersion _
  have : IsFinite (I.subschemeι ≫ f) := IsFinite.instCompScheme _ f
  have himage : f.base '' irreducibleComponent x = Set.univ := by
    have himageClosed : IsClosed (f.base '' irreducibleComponent x) :=
      f.isClosedMap _ isClosed_irreducibleComponent
    refine Set.eq_univ_of_forall fun y => ?_
    have hηy : genericPoint Y ⤳ y := (genericPoint_spec Y).specializes (Set.mem_univ y)
    have hη : genericPoint ↥Y ∈ f.base '' irreducibleComponent x :=
      ⟨x, mem_irreducibleComponent, hx⟩
    exact himageClosed.closure_subset (closure_mono
      (Set.singleton_subset_iff.mpr hη) (specializes_iff_mem_closure.mp hηy))
  have : Surjective (I.subschemeι ≫ f) := ⟨by
    intro y
    obtain ⟨z, hzC, rfl⟩ : y ∈ f.base '' irreducibleComponent x := by
      rw [himage]; exact Set.mem_univ y
    have hzrange : z ∈ Set.range I.subschemeι.base := by
      rw [I.range_subschemeι, hsupport]; exact hzC
    obtain ⟨w, hw⟩ := hzrange
    exact ⟨w, by simpa using congrArg f.base hw⟩⟩
  have hL' : Stacks.Ample.IsAmple I.subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule I.subschemeι L) :=
    Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding
      I.subschemeι L hL (Or.inl ⟨inferInstance, inferInstance⟩)
  obtain ⟨φ, -, hN⟩ := exists_norm_of_finite_surjective_of_normal (I.subschemeι ≫ f)
  let _ : Algebra Y.functionField I.subscheme.functionField := φ.toAlgebra
  have hd : 0 < Module.finrank Y.functionField I.subscheme.functionField := by
    obtain ⟨N⟩ := hN
    exact pos_of_morphismNorm (I.subschemeι ≫ f) N ⟨x, hxSupport⟩
  exact exists_isAmple_of_hasNormOfDegree (I.subschemeι ≫ f) _ hL' hd hN

end Stacks.Divisors

end
