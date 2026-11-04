module

public import Mathlib.Algebra.Module.GradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DirectSum.RangeGrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Stalk

/-!
# The graded module of shifted global sections on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded
`S`-module, and `X = Proj 𝒮`. A homogeneous element of `M` of degree `n` is a degree-zero
element of the shift `M(n)`, hence gives a global section of the sheaf `M(n)~` associated to
`M(n)`. These degreewise maps assemble into a homomorphism of graded `S`-modules

`M ⟶ ⨁_{n ∈ ℤ} Γ(X, M(n)~)`.

The target is graded by the honest groups of global sections, and a homogeneous scalar `a` of
degree `i` sends `Γ(X, M(n)~)` to `Γ(X, M(i + n)~)` by multiplication by `a` in every localized
module fiber: if a section is locally the fraction `m / s` with `m` and `s` homogeneous of
degrees `k + n` and `k`, then `a • m` and `s` are homogeneous of degrees `k + (i + n)` and `k`,
so the pointwise product is again a section of the right sheaf. Those two formulas — the
degreewise map on homogeneous elements and the pointwise scalar action — pin the whole structure
down, and they are what the construction is packaged with.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsComponent`: the group
  `Γ(X, M(n)~)` of global sections of the sheaf associated to the shift `M(n)`.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedModuleGlobalSections`: the direct sum
  `⨁_{n ∈ ℤ} Γ(X, M(n)~)` of all of them.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedModuleGlobalSectionsGrading`: its
  tautological grading, the degree-`n` piece being the image of the `n`-th summand.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedModuleGlobalSectionsDecomposition`: that
  family is an internal grading.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.GlobalSectionsModuleMap`: the `S`-module
  structure on the direct sum together with the graded map from `M`, bundled with the two
  formulas characterizing them.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections`: the action of
  a homogeneous element of degree `i` as a map `Γ(X, M(n)~) → Γ(X, M(i + n)~)`.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections`: the canonical map
  `𝒨 n → Γ(X, M(n)~)`, as an additive homomorphism; this is the displayed map of Tag 0AG2.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.shiftedSectionsGModule`: the resulting external
  graded-module structure of the family of section groups over the family `𝒮`.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.globalSectionsModuleMap`: the canonical datum,
  which is the displayed map of Tag 01MR.

## Main results

* `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_apply`: the
  homogeneous scalar action is pointwise multiplication in the module fibers.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_apply`: the global
  section attached to a homogeneous element of degree `n` has value `m / 1` at every point.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.degreeNToGlobalSections_homogeneousScalar`: the
  degreewise maps are equivariant for the homogeneous scalar actions.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_add_right`,
  `homogeneousScalarGlobalSections_zero_right`,
  `homogeneousScalarGlobalSections_add_left`,
  `homogeneousScalarGlobalSections_zero_left`: bilinearity of the homogeneous scalar action.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.homogeneousScalarGlobalSections_one` and
  `homogeneousScalarGlobalSections_mul`: the unit and associativity laws of the action, with the
  degrees transported by `cast` rather than by the heterogeneous equality of `GradedMonoid`.
* `Stacks.AlgebraicGeometry.ProjShiftedSections.cast_submodule_coe`: transporting an element of
  a graded piece along an equality of degrees does not change the underlying element.

## Implementation notes

The target uses the associated sheaf `M(n)~` of the shifted grading, *not* the twist `M̃(n)` of
the associated sheaf. For a general graded ring these two sheaves differ, and only the former is
available with no hypothesis on `𝒮`; the displayed equation of the source is about the former.

The grading of the direct sum is the tautological one, `DirectSum.rangeGrading`, with the
decomposition instance `DirectSum.rangeGradingDecomposition`; it is a family of `ℤ`-submodules
rather than of additive subgroups, which is what the general construction supplies.

The module structure and the map are packaged in a structure together with the equations
characterizing them, as for the graded ring of twisted global sections, rather than exposed as
bare data: a `Module S (⨁ n, Γ(X, M(n)~))` instance is not unique as data, but it is unique once
its homogeneous scalar action is prescribed pointwise on local fractions.

The external graded module `shiftedSectionsGModule` is built degreewise from
`homogeneousScalarGlobalSections`, and **every one of its six laws is proved before the
structure is assembled, with none of them mentioning `GradedMonoid`.** The four bilinearity
laws leave the degree alone and are plain equalities of sections. The unit and associativity
laws do not: each is an equality between elements of `Γ(X, M(k)~)` for two syntactically
different but equal degrees `k`, so each is stated through `cast` along the equality of degrees,
as `homogeneousScalarGlobalSections_one` and `homogeneousScalarGlobalSections_mul`, and
`Sigma.ext` together with `cast_heq` turns it into the heterogeneous equality the corresponding
field asks for. Assembling the six laws inside the structure instance instead makes one command
out of six unrelated pointwise computations over sheaf-valued types, each of which elaborates
comfortably on its own. The bookkeeping lemma `cast_submodule_coe` is general and not part of
the interface of the construction, but it has to be a public declaration: it is named in the
exposed body of `shiftedSectionsGModule`. The `S`-module structure on the direct sum is then
obtained from `DirectSum.Gmodule.module` by restricting scalars along
`DirectSum.decomposeRingEquiv`, and the map out of `M` by composing with
`GradedModule.linearEquiv`.

The action of `ℕ`-degrees on `ℤ`-degrees is the scoped `Stacks.GradedLocalization.instVAddNatInt`,
the one the global-sections map was constructed with; `GradedModule.isModule` and
`GradedModule.linearEquiv` additionally require it to be an `AddAction`, for which Mathlib has no
instance, so one is supplied file-locally here.

## References

* [Stacks Project, Equation 27.9.0.2, Tag 0AG2](https://stacks.math.columbia.edu/tag/0AG2)
* [Stacks Project, Equation 27.10.0.6, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (ModuleFiber associatedModuleSheaf associatedModuleSheafSectionsEquiv moduleSections)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections
  (associatedModuleSheafStalkEquiv_germ degreeZeroToGlobalSections
    degreeZeroToGlobalSections_stalk)
open Stacks.GradedModule (shiftedGrading)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjShiftedSections

universe u v w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- Translation of `ℤ` by the natural numbers, as an additive action. Mathlib has no such
instance: the `VAdd ℕ ℤ` of `Stacks.GradedLocalization` is a scoped choice of grading action, and
`GradedModule.isModule` and `GradedModule.linearEquiv` ask for it to be an `AddAction`. -/
local instance : AddAction ℕ ℤ where
  toVAdd := inferInstance
  add_vadd i j n := by
    change ((i + j : ℕ) : ℤ) + n = (i : ℤ) + ((j : ℤ) + n)
    rw [Nat.cast_add, Int.add_assoc]
  zero_vadd n := Int.zero_add n

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

/-- The degree-`n` component of the graded module of shifted global sections: the global
sections of the sheaf associated to the shift `M(n)`. -/
public abbrev shiftedSectionsComponent (n : ℤ) : Type _ :=
  (associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n)).val.obj (op ⊤)

/-- Global sections of the associated sheaves of all shifts of a graded module, as a direct
sum over the integers. -/
public abbrev shiftedModuleGlobalSections : Type _ :=
  ⨁ n : ℤ, shiftedSectionsComponent 𝒮 𝒨 n

/-- The degree-`n` piece of the grading on shifted global sections: the image of the `n`-th
summand in the direct sum. -/
public def shiftedModuleGlobalSectionsGrading (n : ℤ) :
    Submodule ℤ (shiftedModuleGlobalSections 𝒮 𝒨) :=
  DirectSum.rangeGrading ℤ (fun k => shiftedSectionsComponent 𝒮 𝒨 k) n

/-- Every shifted global section decomposes uniquely into homogeneous parts. -/
public noncomputable instance shiftedModuleGlobalSectionsDecomposition :
    DirectSum.Decomposition (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) :=
  DirectSum.rangeGradingDecomposition ℤ (fun k => shiftedSectionsComponent 𝒮 𝒨 k)

/-- The canonical `S`-module structure on the shifted global sections together with the graded
map from `M`, bundled with the formulas that characterize them: in each degree the map is the
canonical map from the homogeneous elements, and the homogeneous scalar action is pointwise
multiplication in the module fibers. -/
public structure GlobalSectionsModuleMap where
  /-- The `S`-module structure on `⨁ n, Γ(Proj 𝒮, M(n)~)`. -/
  moduleInst : Module S (shiftedModuleGlobalSections 𝒮 𝒨)
  /-- The action is compatible with the gradings of `S` and of the direct sum. -/
  gradedSMul : letI := moduleInst
    SetLike.GradedSMul 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨)
  /-- The canonical `S`-linear map `M → ⨁ n, Γ(Proj 𝒮, M(n)~)`. -/
  hom : letI := moduleInst
    M →ₗ[S] shiftedModuleGlobalSections 𝒮 𝒨
  /-- On a homogeneous element of degree `n` the map is the canonical global section of
  `M(n)~`, placed in the degree-`n` summand. -/
  map_homogeneous : letI := moduleInst
    ∀ (n : ℤ) (m : 𝒨 n), hom m.1 =
      DirectSum.of _ n
        (degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n)
          ⟨m.1, by simpa only [shiftedGrading, zero_add] using m.2⟩)
  /-- A homogeneous scalar of degree `i` acts on the degree-`n` summand by multiplication in
  every localized module fiber, landing in the degree-`i + n` summand. -/
  smul_homogeneous : letI := moduleInst
    ∀ (i : ℕ) (n : ℤ) (a : 𝒮 i) (s : shiftedSectionsComponent 𝒮 𝒨 n)
      (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))),
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).toFun
        (DirectSum.component ℤ ℤ _ ((i : ℤ) + n) ((a : S) •
          (DirectSum.of _ n s : shiftedModuleGlobalSections 𝒮 𝒨)))).1 x =
        (a : S) • ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun s).1 x

/-- Transporting an element of a graded piece along an equality of degrees does not change the
underlying element of the ambient module. -/
public theorem cast_submodule_coe {ι R V : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V]
    (N : ι → Submodule R V) {i j : ι} (h : i = j) (x : N i) :
    ((cast (congrArg (fun k => (N k : Type _)) h) x : N j) : V) = x := by
  cases h
  rfl

/-- Multiplication by a homogeneous element of degree `i`, as a morphism of associated sheaves
`M(n)~ ⟶ M(i + n)~`: it is degree-preserving from the shift by `n` to the shift by `i + n`. -/
private noncomputable def homogeneousScalarSheafMap (i : ℕ) (n : ℤ) (a : 𝒮 i) :
    associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 n) ⟶
      associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) := by
  let φ : M →ₗ[S] M :=
    { toFun := fun m => (a : S) • m
      map_add' := fun x y => smul_add (a : S) x y
      map_smul' := fun c m => smul_comm (a : S) c m }
  exact ProjSheafFunctoriality.associatedModuleSheafMap 𝒮
    (shiftedGrading 𝒨 n)
    (shiftedGrading 𝒨 ((i : ℤ) + n)) φ (by
      intro k m hm
      have h := SetLike.GradedSMul.smul_mem (A := 𝒮)
        (B := shiftedGrading 𝒨 n) a.2 hm
      change (a : S) • m ∈ 𝒨 (((i : ℤ) + k) + n) at h
      change (a : S) • m ∈ 𝒨 (k + ((i : ℤ) + n))
      convert h using 1
      congr 1
      omega)

/-- Multiplication by a homogeneous element of degree `i` on global sections, as a map
`Γ(Proj 𝒮, M(n)~) → Γ(Proj 𝒮, M(i + n)~)`: a local fraction `m / s` of degrees `k + n` and `k`
goes to the local fraction `a • m / s` of degrees `k + (i + n)` and `k`. -/
public noncomputable def homogeneousScalarGlobalSections (i : ℕ) (n : ℤ)
    (a : 𝒮 i) :
    shiftedSectionsComponent 𝒮 𝒨 n → shiftedSectionsComponent 𝒮 𝒨 ((i : ℤ) + n) := by
  let e₁ := associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤
  let e₂ := associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤
  intro s
  refine e₂.symm.toFun ⟨fun x => (a : S) • (e₁.toFun s).1 x, ?_⟩
  intro x
  obtain ⟨U, hxU, iU, k, m, d, hm, hd, hden, hrep⟩ := (e₁.toFun s).2 x
  have hsm := SetLike.GradedSMul.smul_mem (A := 𝒮)
    (B := shiftedGrading 𝒨 n) a.2 hm
  change (a : S) • m ∈ 𝒨 (((i : ℤ) + (k : ℤ)) + n) at hsm
  refine ⟨U, hxU, iU, k, (a : S) • m, d, ?_, hd, hden, ?_⟩
  · have hidx : ((i : ℤ) + (k : ℤ)) + n =
        (k : ℤ) + ((i : ℤ) + n) := by omega
    rw [hidx] at hsm
    exact hsm
  · intro y
    change (a : S) • (e₁.toFun s).1 (iU y) = _
    have hy := hrep y
    change (e₁.toFun s).1 (iU y) = _ at hy
    rw [hy]
    have hypt : (iU y).1 = y.1 := rfl
    change (a : S) • LocalizedModule.mk m
        (⟨d, by simpa [hypt] using hden y⟩ :
          (iU y).1.asHomogeneousIdeal.toIdeal.primeCompl) = _
    rw [← algebraMap_smul (Localization (iU y).1.asHomogeneousIdeal.toIdeal.primeCompl)]
    rw [← Localization.mk_algebraMap (A := S) (a : S)]
    rw [LocalizedModule.mk_smul_mk]
    simp

/-- Two shifted global sections are equal when their values in every module fiber agree. -/
private theorem shifted_sections_ext (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒮 𝒨]
    {k : ℤ} {s t : shiftedSectionsComponent 𝒮 𝒨 k}
    (h : ∀ x, ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).toFun s).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).toFun t).1 x) :
    s = t :=
  (associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).injective
    (Subtype.ext (funext h))

/-- The fiber values of a sum of shifted global sections are the sums of the fiber values. -/
private theorem shifted_sections_add_apply (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒮 𝒨]
    {k : ℤ} (s t : shiftedSectionsComponent 𝒮 𝒨 k) (x) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).toFun (s + t)).1 x =
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).toFun s).1 x +
        ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).toFun t).1 x :=
  congrArg (fun q => q.1 x)
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 k) ⊤).map_add s t)

/-- Transporting a shifted global section along an equality of degrees does not change its fiber
values. -/
private theorem shifted_sections_cast_apply (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒮 𝒨]
    {i j : ℤ} (h : i = j)
    (s : shiftedSectionsComponent 𝒮 𝒨 i) (x) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 j) ⊤).toFun
      (cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) h) s)).1 x =
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 i) ⊤).toFun s).1 x := by
  cases h
  rfl

omit [Decomposition 𝒨] in
/-- The homogeneous scalar action is pointwise multiplication in the localized module
fibers. -/
public theorem homogeneousScalarGlobalSections_apply (i : ℕ) (n : ℤ)
    (a : 𝒮 i) (s : shiftedSectionsComponent 𝒮 𝒨 n)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).toFun
      (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s)).1 x =
    (a : S) • (((associatedModuleSheafSectionsEquiv 𝒮
      (shiftedGrading 𝒨 n) ⊤).toFun s).1 x) := rfl

/-- The canonical map from the degree-`n` homogeneous elements of `M` to the global sections of
`M(n)~`, as an additive homomorphism: it is the degree-zero global-sections map of the shift.
This is the map `Mₙ → Γ(Proj(S), M(n)~)` of Tag 0AG2, obtained from the degree-zero map of Tag
0AG1 for the grading of `M(n)` and the identification `M(n)₀ = Mₙ` of
`Stacks.GradedModule.shiftedGrading_zero`. -/
@[stacks 0AG2 "map_degree_n_global_sections", ega "II 3.3.2" "partial, special case"]
public noncomputable def degreeNToGlobalSections (n : ℤ) :
    𝒨 n →+ shiftedSectionsComponent 𝒮 𝒨 n where
  toFun m := degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n)
    ⟨m.1, by simpa only [shiftedGrading, zero_add] using m.2⟩
  map_zero' := by
    change degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n) 0 = 0
    exact map_zero _
  map_add' m m' := by
    let f := degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n)
    let m₀ : ↥(shiftedGrading 𝒨 n 0) :=
      ⟨m.1, by simpa only [shiftedGrading, zero_add] using m.2⟩
    let m'₀ : ↥(shiftedGrading 𝒨 n 0) :=
      ⟨m'.1, by simpa only [shiftedGrading, zero_add] using m'.2⟩
    have hm : (⟨(m + m').1, by simpa only [shiftedGrading, zero_add] using
        (m + m').2⟩ : ↥(shiftedGrading 𝒨 n 0)) = m₀ + m'₀ := by
      apply Subtype.ext
      rfl
    change f (⟨(m + m').1, _⟩ : ↥(shiftedGrading 𝒨 n 0)) = _
    rw [hm]
    exact map_add f m₀ m'₀

omit [Decomposition 𝒨] in
/-- The global section attached to a homogeneous element of degree `n` has value `m / 1` at
every point of `Proj 𝒮`. -/
public theorem degreeNToGlobalSections_apply (n : ℤ) (m : 𝒨 n)
    (x : ProjectiveSpectrum.top 𝒮) :
    ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun
        (degreeNToGlobalSections 𝒮 𝒨 n m)).1 ⟨x, trivial⟩ =
      LocalizedModule.mk m.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
  let m₀ : ↥((shiftedGrading 𝒨 n) 0) :=
    ⟨m.1, by simpa only [shiftedGrading, Int.zero_add] using m.2⟩
  have hsection :
      ((associatedModuleSheafSectionsEquiv 𝒮 (shiftedGrading 𝒨 n) ⊤).toFun
        (degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n) m₀)).1 ⟨x, by simp⟩ =
        LocalizedModule.mk m.1 (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    (associatedModuleSheafStalkEquiv_germ 𝒮 (shiftedGrading 𝒨 n) x ⊤ (by simp)
      (degreeZeroToGlobalSections 𝒮 (shiftedGrading 𝒨 n) m₀)).symm.trans
      (degreeZeroToGlobalSections_stalk (𝒮 := 𝒮) (𝒨 := shiftedGrading 𝒨 n) x m₀)
  simpa [degreeNToGlobalSections, m₀, shiftedGrading] using hsection

omit [Decomposition 𝒨] in
/-- The degreewise maps are equivariant: the global section of a homogeneous multiple `a • m` is
the homogeneous scalar action of `a` on the global section of `m`. -/
public theorem degreeNToGlobalSections_homogeneousScalar (i : ℕ) (n : ℤ)
    (a : 𝒮 i) (m : 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n a
      (degreeNToGlobalSections 𝒮 𝒨 n m) =
      degreeNToGlobalSections 𝒮 𝒨 ((i : ℤ) + n)
        ⟨(a : S) • m.1, by
          have h := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) a.2 m.2
          simpa only [show (i : ℕ) +ᵥ n = (i : ℤ) + n from rfl] using h⟩ := by
  apply shifted_sections_ext
  intro x
  rw [homogeneousScalarGlobalSections_apply, degreeNToGlobalSections_apply,
    degreeNToGlobalSections_apply,
    ← algebraMap_smul (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl),
    ← Localization.mk_algebraMap (A := S) (a : S), LocalizedModule.mk_smul_mk]
  simp

omit [Decomposition 𝒨] in
/-- A homogeneous scalar of degree `0` whose underlying element is `1` acts as the identity on
shifted global sections, after the degree `0 + n` is identified with `n`. -/
public theorem homogeneousScalarGlobalSections_one (n : ℤ) (a : 𝒮 0) (ha : (a : S) = 1)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 0 n a s =
      cast (congrArg (shiftedSectionsComponent 𝒮 𝒨) (Int.zero_add n).symm) s := by
  apply shifted_sections_ext
  intro x
  rw [homogeneousScalarGlobalSections_apply, ha, one_smul]
  exact (shifted_sections_cast_apply 𝒮 𝒨 (Int.zero_add n).symm s x).symm

omit [Decomposition 𝒨] in
/-- A product of homogeneous scalars of degrees `i` and `j` acts as the composite of the two
actions, after the degree `(i + j) + n` is identified with `i + (j + n)`. -/
public theorem homogeneousScalarGlobalSections_mul (i j : ℕ) (n : ℤ) (a : 𝒮 i) (b : 𝒮 j)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 (i + j) n
        ⟨(a : S) * (b : S), SetLike.mul_mem_graded a.2 b.2⟩ s =
      cast (congrArg (shiftedSectionsComponent 𝒮 𝒨)
          (show (i : ℤ) + ((j : ℤ) + n) = ((i + j : ℕ) : ℤ) + n by omega))
        (homogeneousScalarGlobalSections 𝒮 𝒨 i ((j : ℤ) + n) a
          (homogeneousScalarGlobalSections 𝒮 𝒨 j n b s)) := by
  apply shifted_sections_ext
  intro x
  refine (homogeneousScalarGlobalSections_apply ..).trans (Eq.trans ?_
    (shifted_sections_cast_apply 𝒮 𝒨 (by omega) _ x).symm)
  rw [homogeneousScalarGlobalSections_apply, homogeneousScalarGlobalSections_apply, mul_smul]

omit [Decomposition 𝒨] in
/-- The homogeneous scalar action is additive in the section. -/
public theorem homogeneousScalarGlobalSections_add_right (i : ℕ) (n : ℤ) (a : 𝒮 i)
    (s t : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n a (s + t) =
      homogeneousScalarGlobalSections 𝒮 𝒨 i n a s +
        homogeneousScalarGlobalSections 𝒮 𝒨 i n a t := by
  apply shifted_sections_ext
  intro x
  simp only [shifted_sections_add_apply, homogeneousScalarGlobalSections_apply, smul_add]

omit [Decomposition 𝒨] in
/-- A homogeneous scalar sends the zero section to the zero section. -/
public theorem homogeneousScalarGlobalSections_zero_right (i : ℕ) (n : ℤ) (a : 𝒮 i) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n a
        (0 : shiftedSectionsComponent 𝒮 𝒨 n) = 0 := by
  apply shifted_sections_ext
  intro x
  rw [homogeneousScalarGlobalSections_apply]
  simp

omit [Decomposition 𝒨] in
/-- The homogeneous scalar action is additive in the scalar. -/
public theorem homogeneousScalarGlobalSections_add_left (i : ℕ) (n : ℤ) (a b : 𝒮 i)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n (a + b) s =
      homogeneousScalarGlobalSections 𝒮 𝒨 i n a s +
        homogeneousScalarGlobalSections 𝒮 𝒨 i n b s := by
  apply shifted_sections_ext
  intro x
  simp only [shifted_sections_add_apply, homogeneousScalarGlobalSections_apply,
    AddMemClass.coe_add, add_smul]

omit [Decomposition 𝒨] in
/-- The zero homogeneous scalar annihilates every shifted global section. -/
public theorem homogeneousScalarGlobalSections_zero_left (i : ℕ) (n : ℤ)
    (s : shiftedSectionsComponent 𝒮 𝒨 n) :
    homogeneousScalarGlobalSections 𝒮 𝒨 i n 0 s = 0 := by
  apply shifted_sections_ext
  intro x
  rw [homogeneousScalarGlobalSections_apply]
  simp

/-- The family of shifted global-section groups, with the homogeneous scalar action, is an
external graded module over the family of homogeneous pieces of `S`. -/
@[instance_reducible] public noncomputable def shiftedSectionsGModule :
    DirectSum.Gmodule (fun i : ℕ => 𝒮 i)
      (fun n : ℤ => shiftedSectionsComponent 𝒮 𝒨 n) := by
  classical
  let A : ℕ → Type _ := fun i => 𝒮 i
  letI : DirectSum.GCommRing A := inferInstance
  refine {
    smul := fun {i n} a s => homogeneousScalarGlobalSections 𝒮 𝒨 i n a s
    one_smul := ?_
    mul_smul := ?_
    smul_add := fun {i n} a s t =>
      homogeneousScalarGlobalSections_add_right 𝒮 𝒨 i n a s t
    smul_zero := fun {i n} a => homogeneousScalarGlobalSections_zero_right 𝒮 𝒨 i n a
    add_smul := fun {i n} a b s =>
      homogeneousScalarGlobalSections_add_left 𝒮 𝒨 i n a b s
    zero_smul := fun {i n} s => homogeneousScalarGlobalSections_zero_left 𝒮 𝒨 i n s }
  · intro ⟨n, s⟩
    have hone : ((GradedMonoid.GOne.one (A := A) : 𝒮 0) : S) = 1 := by
      simp only [SetLike.coe_gOne]
    exact Sigma.ext (Int.zero_add n)
      ((heq_of_eq (homogeneousScalarGlobalSections_one 𝒮 𝒨 n _ hone s)).trans
        (cast_heq _ _))
  · intro ⟨i, a⟩ ⟨j, b⟩ ⟨n, s⟩
    exact Sigma.ext (show ((i + j : ℕ) : ℤ) + n = (i : ℤ) + ((j : ℤ) + n) by omega)
      ((heq_of_eq (homogeneousScalarGlobalSections_mul 𝒮 𝒨 i j n a b s)).trans
        (cast_heq _ _))

/-- **The canonical map of graded `S`-modules `M → ⨁_{n ∈ ℤ} Γ(Proj 𝒮, M(n)~)`.** In degree `n`
it is the canonical map from the homogeneous elements of degree `n`, and a homogeneous scalar
acts pointwise on local fractions; those two formulas determine the whole datum. -/
@[stacks 01MR]
public noncomputable def globalSectionsModuleMap : GlobalSectionsModuleMap 𝒮 𝒨 := by
  classical
  let A : ℕ → Type _ := fun i => 𝒮 i
  let B : ℤ → Type _ := fun n => shiftedSectionsComponent 𝒮 𝒨 n
  let R := ⨁ i, A i
  let T := shiftedModuleGlobalSections 𝒮 𝒨
  let source := ⨁ n : ℤ, 𝒨 n
  letI : DirectSum.GCommRing A := inferInstance
  letI : DirectSum.Gmodule A B := shiftedSectionsGModule 𝒮 𝒨
  letI : Module R T := DirectSum.Gmodule.module A B
  let moduleInst : Module S T :=
    Module.compHom (M := T) (DirectSum.decomposeRingEquiv 𝒮).toRingHom
  letI : DirectSum.Gmodule A (fun n : ℤ => 𝒨 n) := inferInstance
  letI : Module R source := DirectSum.Gmodule.module A (fun n : ℤ => 𝒨 n)
  letI : Module S source := GradedModule.isModule 𝒮 𝒨
  let sourceEquiv : M ≃ₗ[S] source := GradedModule.linearEquiv 𝒮 𝒨
  let fAdd : source →+ T := DirectSum.toAddMonoid (fun n =>
    (DirectSum.of B n).comp (degreeNToGlobalSections 𝒮 𝒨 n))
  have fAdd_of (n : ℤ) (m : 𝒨 n) :
      fAdd (DirectSum.of (fun n : ℤ => 𝒨 n) n m) =
        DirectSum.of B n (degreeNToGlobalSections 𝒮 𝒨 n m) := by
    dsimp [fAdd]
    exact DirectSum.toAddMonoid_of
      (fun k => (DirectSum.of B k).comp (degreeNToGlobalSections 𝒮 𝒨 k)) n m
  let fLinear : source →ₗ[R] T := {
    toFun := fAdd
    map_add' := fAdd.map_add
    map_smul' := by
      intro r z
      induction r using DirectSum.induction_on with
      | zero => simp only [zero_smul, map_zero]
      | of i a =>
        induction z using DirectSum.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | of j b =>
          calc
            fAdd (DirectSum.of A i a • DirectSum.of (fun j : ℤ => 𝒨 j) j b) =
                fAdd (DirectSum.of (fun j : ℤ => 𝒨 j) (i +ᵥ j)
                  (GradedMonoid.GSMul.smul
                    (A := fun i : ℕ => 𝒮 i) (M := fun j : ℤ => 𝒨 j) a b)) := by
                  rw [DirectSum.Gmodule.of_smul_of]
            _ = DirectSum.of B (i +ᵥ j)
                  (degreeNToGlobalSections 𝒮 𝒨 (i +ᵥ j)
                    (GradedMonoid.GSMul.smul
                      (A := fun i : ℕ => 𝒮 i) (M := fun j : ℤ => 𝒨 j) a b)) :=
                  fAdd_of _ _
            _ = DirectSum.of B (i +ᵥ j)
                  (homogeneousScalarGlobalSections 𝒮 𝒨 i j a
                    (degreeNToGlobalSections 𝒮 𝒨 j b)) := by
                  exact congrArg (DirectSum.of B (i +ᵥ j))
                    (degreeNToGlobalSections_homogeneousScalar 𝒮 𝒨 i j a b).symm
            _ = (RingHom.id R) (DirectSum.of A i a) •
                  fAdd (DirectSum.of (fun j : ℤ => 𝒨 j) j b) := by
                  rw [RingHom.id_apply, fAdd_of,
                    DirectSum.Gmodule.of_smul_of]
                  apply congrArg (DirectSum.of B (i +ᵥ j))
                  change homogeneousScalarGlobalSections 𝒮 𝒨 i j a
                      (degreeNToGlobalSections 𝒮 𝒨 j b) =
                    GradedMonoid.GSMul.smul a
                      (degreeNToGlobalSections 𝒮 𝒨 j b)
                  rfl
        | add z w hz hw =>
          simp only [map_add, smul_add, hz, hw]
      | add r s hr hs =>
        simp only [map_add, add_smul, hr, hs] }
  let hom : M →ₗ[S] T :=
    { toFun := fun m => fLinear (sourceEquiv m)
      map_add' := by intro x y; simp
      map_smul' := by
        intro c m
        rw [sourceEquiv.map_smul]
        have hs : (c : S) • sourceEquiv m =
            DirectSum.decompose 𝒮 c • sourceEquiv m := rfl
        rw [hs]
        rw [fLinear.map_smul]
        rfl }
  let gradedSMul : letI := moduleInst
      SetLike.GradedSMul 𝒮 (shiftedModuleGlobalSectionsGrading 𝒮 𝒨) := by
    let : Module S T := moduleInst
    refine ⟨?_⟩
    intro i n a b ha hb
    let a' : 𝒮 i := ⟨a, ha⟩
    obtain ⟨s, rfl⟩ := (DirectSum.mem_rangeGrading ℤ B n b).mp hb
    refine (DirectSum.mem_rangeGrading ℤ B ((i : ℤ) + n) _).mpr
      ⟨homogeneousScalarGlobalSections 𝒮 𝒨 i n a' s, ?_⟩
    change (DirectSum.decompose 𝒮 a) • DirectSum.of B n s =
      DirectSum.of B ((i : ℤ) + n) (homogeneousScalarGlobalSections 𝒮 𝒨 i n a' s)
    rw [DirectSum.decompose_of_mem 𝒮 ha,
      DirectSum.Gmodule.of_smul_of]
    rfl
  letI : Module S T := moduleInst
  refine ⟨moduleInst, gradedSMul, hom, ?_, ?_⟩
  · intro n m
    change fLinear (sourceEquiv m.1) = _
    have hm : sourceEquiv m.1 = DirectSum.of (fun n : ℤ => 𝒨 n) n m := by
      simp [sourceEquiv, GradedModule.linearEquiv]
    rw [hm]
    dsimp [fLinear]
    dsimp [fAdd]
    rw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
    rfl
  · intro i n a s x
    change ((associatedModuleSheafSectionsEquiv 𝒮
      (shiftedGrading 𝒨 ((i : ℤ) + n)) ⊤).toFun
      (DirectSum.component ℤ ℤ B ((i : ℤ) + n)
        ((a : S) • (DirectSum.of B n s : T)))).1 x = _
    have hscalar : (a : S) • (DirectSum.of B n s : T) =
        DirectSum.of B ((i : ℤ) + n) (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s) := by
      change (DirectSum.decompose 𝒮 (a : S)) • DirectSum.of B n s = _
      rw [DirectSum.decompose_coe 𝒮 a, DirectSum.Gmodule.of_smul_of]
      rfl
    rw [hscalar]
    have hcomp : DirectSum.component ℤ ℤ B ((i : ℤ) + n)
        (DirectSum.of B ((i : ℤ) + n)
          (homogeneousScalarGlobalSections 𝒮 𝒨 i n a s)) =
        homogeneousScalarGlobalSections 𝒮 𝒨 i n a s := by
      rw [← DirectSum.lof_eq_of (R := ℤ)]
      exact DirectSum.component.lof_self (R := ℤ) (M := B)
        ((i : ℤ) + n) _
    rw [hcomp]
    exact homogeneousScalarGlobalSections_apply 𝒮 𝒨 i n a s x

end Stacks.AlgebraicGeometry.ProjShiftedSections

end
