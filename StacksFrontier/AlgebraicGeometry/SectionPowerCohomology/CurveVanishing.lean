module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.CokernelSupport
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.Localization
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.Topology.Dimension.Krull

/-!
# `H¹` dies along the powers of a section with affine nonvanishing open

This is the third paragraph of the proof of [Stacks, Tag 0B5X]. Let `X` be a proper curve over a
field `k`, let `ℒ` be an invertible `𝒪_X`-module with a global section `s` whose nonvanishing
open `X_s` is nonempty and affine, and let `ℱ` be a coherent quasi-coherent `𝒪_X`-module. Then
`H¹(X, ℱ ⊗ ℒ^{⊗ N}) = 0` for some `N ≥ 1`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `surjective_cohomologyOverFieldMap_one_of_isZero_cokernel`: **the surjectivity step.** For any
  morphism of modules whose cokernel has vanishing `H¹`, on a scheme whose cohomology vanishes in
  degree two, the induced map on `H¹` is surjective. Monomorphy is not needed.
* `surjective_cohomologyOverFieldMap_one_twistHom`: the same at multiplication by `sⁿ`, whose
  cokernel is supported in the closed complement of `X_s`.
* `exists_isZero_cohomologyOverField_one_twist`: **the conclusion** — some positive power of `s`
  annihilates all of `H¹(X, ℱ)` and the corresponding twist has vanishing `H¹`.

## The argument

**Surjectivity without monomorphy.** Factor `φ : 𝒜 ⟶ ℬ` through its image. The long exact
sequence of `0 ⟶ ker ⟶ 𝒜 ⟶ im ⟶ 0` has `H¹(𝒜) ⟶ H¹(im) ⟶ H²(ker)`, and `H²` vanishes on a
curve, so the first map is onto; the long exact sequence of `0 ⟶ im ⟶ ℬ ⟶ coker ⟶ 0` has
`H¹(im) ⟶ H¹(ℬ) ⟶ H¹(coker)`, and `H¹(coker)` vanishes by hypothesis, so the first map is onto.
Their composite is `H¹(φ)`, by `AlgebraicGeometry.cohomologyOverFieldMap_comp` and
`CategoryTheory.Abelian.image.fac`. Nothing about `φ` enters but its cokernel, which is why the
injectivity the source asserts is not needed.

**The cokernel of multiplication by `sⁿ`.** Its support misses `X_s`
(`Stacks.Cohomology.TwistedLocalizationMap.supp_cokernel_twistHom_subset_compl`), hence is
contained in the closed set `X ∖ X_s`, which is a proper closed subset of an irreducible space
of dimension at most one and so has dimension at most zero
(`AlgebraicGeometry.topologicalKrullDim_le_zero_of_isClosed_of_ne_univ`). The cokernel is
coherent, so [Stacks, Tag 0AYT] (3) applies and its `H¹` vanishes.

**The chain of kernels.** `H¹(X, ℱ)` is a finite-dimensional `k`-vector space
([Stacks, Tag 02O6]). Multiplication by `sⁿ` on it is the `k`-linear
`AlgebraicGeometry.cohomologyOverFieldMap`, and under the comparison of
`../AmpleDegreeCriterion/CohomologyBridge.lean` it is the `mulPow` of the twisted localization,
where two facts are available: every class is killed by some power of `s` ([Stacks, Tag 01XR],
`Stacks.SheafOfModules.exists_mulPow_eq_zero_of_isAffineOpen_nonvanishingOpen`)
and the exponents that kill a given class are upward closed
(`Stacks.Cohomology.TwistedLocalizationMap.actPow_mulPow`). The kernels are therefore an
increasing chain of `k`-subspaces whose union is everything; a finite spanning set of
`H¹(X, ℱ)` is contained in one of them, so that one is everything. Multiplication by `s^N` is
then both zero and onto `H¹(X, ℱ ⊗ ℒ^{⊗ N})`, which must vanish.

## Implementation notes

**The exponent is pushed up to be positive.** The spanning set may be empty, in which case the
chain argument returns `N = 0`; `max N 1` is used instead, which still annihilates everything
because the kernels increase.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingOpen)
open Stacks.Cohomology.TwistedGradedModule (twist)
open Stacks.Cohomology.TwistedLocalizationMap (twistHom mulPow actPow)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Surjectivity on `H¹` from the cokernel alone -/

/-- **A morphism whose cokernel has vanishing `H¹` induces a surjection on `H¹`**, on a scheme
whose cohomology vanishes in degree two. The morphism is not assumed to be a monomorphism: it is
factored through its image, and the two short exact sequences of that factorisation give the two
surjections whose composite is the map on `H¹`. -/
public theorem surjective_cohomologyOverFieldMap_one_of_isZero_cokernel [IsProper f]
    {M N : X.Modules} (φ : M ⟶ N)
    (htwo : ∀ G : X.Modules, IsZero (cohomologyOverField k f G 2))
    (hcoker : IsZero (cohomologyOverField k f (cokernel φ) 1)) :
    Function.Surjective (cohomologyOverFieldMap k f φ 1) := by
  have hS : ∀ {A B : X.Modules} (g : A ⟶ B) [Epi g], (ShortComplex.kernelSequence g).ShortExact :=
    fun g => .mk' (ShortComplex.kernelSequence_exact g) inferInstance (inferInstanceAs (Epi g))
  have hS₁ := hS (Abelian.factorThruImage φ)
  have hS₂ := hS (cokernel.π φ)
  obtain ⟨d₁, -, -, hgd₁, -⟩ := exists_cohomologyOverField_longExactSequence k f hS₁
  obtain ⟨d₂, -, hfg₂, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS₂
  have h₁ : Function.Surjective
      (cohomologyOverFieldMap k f (Abelian.factorThruImage φ) 1) := by
    have _ := ModuleCat.subsingleton_of_isZero
      (htwo (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁)
    exact fun y => (hgd₁ 1 y).1 (Subsingleton.elim _ _)
  have h₂ : Function.Surjective
      (cohomologyOverFieldMap k f (Abelian.image.ι φ) 1) := by
    have _ := ModuleCat.subsingleton_of_isZero
      (show IsZero (cohomologyOverField k f
        (ShortComplex.kernelSequence (cokernel.π φ)).X₃ 1) from hcoker)
    exact fun y => (hfg₂ 1 y).1 (Subsingleton.elim _ _)
  have hcomp : cohomologyOverFieldMap k f (Abelian.factorThruImage φ) 1 ≫
      cohomologyOverFieldMap k f (Abelian.image.ι φ) 1 = cohomologyOverFieldMap k f φ 1 := by
    rw [← cohomologyOverFieldMap_comp]
    exact congrArg (fun ψ => cohomologyOverFieldMap k f ψ 1) (Abelian.image.fac φ)
  intro z
  obtain ⟨y, hy⟩ := h₂ z
  obtain ⟨x, hx⟩ := h₁ y
  refine ⟨x, ?_⟩
  have hxz : (cohomologyOverFieldMap k f (Abelian.factorThruImage φ) 1 ≫
      cohomologyOverFieldMap k f (Abelian.image.ι φ) 1) x = z := by
    rw [ConcreteCategory.comp_apply, hx, hy]
  rwa [hcomp] at hxz

/-! ### Multiplication by a power of a section -/

section Section

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections)

/-- **Multiplication by `sⁿ` is surjective on `H¹` of a coherent module on a proper curve**, as
soon as `X_s` is nonempty. Its cokernel is supported in the closed complement of `X_s`, a proper
closed subset of an irreducible space of dimension at most one, so its `H¹` vanishes by
[Stacks, Tag 0AYT] (3); the cohomology of `X` vanishes in degree two by [Stacks, Tag 02UZ]. -/
public theorem surjective_cohomologyOverFieldMap_one_twistHom [IsProper f]
    [IrreducibleSpace (X : Type u)] (hdim : topologicalKrullDim X ≤ 1)
    (hne : (↑(nonvanishingOpen L s) : Set X).Nonempty)
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) (n : ℕ) :
    Function.Surjective (cohomologyOverFieldMap k f (twistHom X L s F n) 1) := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ := hF
  have hinvPow : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.SheafOfModules.TensorPower.tensorPower (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) L (n : ℤ)) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ L (n : ℤ)
  have _ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.SheafOfModules.TensorPower.tensorPower (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) L (n : ℤ)) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hinvPow
  have _ : _root_.SheafOfModules.IsCoherent (twist X L F (n : ℤ)) :=
    SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F _
  have _ : (cokernel (twistHom X L s F n)).IsCoherent := isCoherent_cokernel _
  have hcompl : (↑(nonvanishingOpen L s) : Set X)ᶜ ≠ Set.univ :=
    Set.compl_ne_univ.mpr hne
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (cokernel (twistHom X L s F n))) ≤ 0 :=
    le_trans
      (_root_.topologicalKrullDim_le_of_subset
        (Stacks.Cohomology.TwistedLocalizationMap.supp_cokernel_twistHom_subset_compl
          X L s F n))
      (topologicalKrullDim_le_zero_of_isClosed_of_ne_univ hdim _
        (nonvanishingOpen L s).isOpen.isClosed_compl hcompl)
  exact surjective_cohomologyOverFieldMap_one_of_isZero_cokernel k f (twistHom X L s F n)
    (fun G => isZero_cohomologyOverField_of_topologicalKrullDim_le k f G (d := 1)
      (by exact_mod_cast hdim) (by omega))
    (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k f
      (cokernel (twistHom X L s F n)) hsupp 1 Nat.one_pos)

/-- **Multiplication by `sⁿ` on `H¹`, in the two spellings of cohomology.** The `k`-linear map of
`AlgebraicGeometry.cohomologyOverFieldMap` kills a class exactly when the `mulPow` of the twisted
localization kills its image under the comparison of
`../AmpleDegreeCriterion/CohomologyBridge.lean`. -/
public theorem cohomologyOverFieldMap_twistHom_eq_zero_iff (F : X.Modules) (n : ℕ)
    (ξ : (cohomologyOverField k f F 1 : Type u)) :
    cohomologyOverFieldMap k f (twistHom X L s F n) 1 ξ = 0 ↔
      mulPow X L s F 1 ⊤ n (cohomologyOverFieldAddEquivHgroup k f F 1 ξ) = 0 := by
  have hnat := cohomologyOverFieldAddEquivHgroup_naturality k f (twistHom X L s F n) 1 ξ
  rw [show mulPow X L s F 1 ⊤ n (cohomologyOverFieldAddEquivHgroup k f F 1 ξ) =
      cohomologyOverFieldAddEquivHgroup k f (twist X L F (n : ℤ)) 1
        (cohomologyOverFieldMap k f (twistHom X L s F n) 1 ξ) from hnat.symm]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h]
    exact map_zero _
  · exact (cohomologyOverFieldAddEquivHgroup k f (twist X L F (n : ℤ)) 1).injective
      (h.trans (map_zero _).symm)

/-- **The exponents of `s` that kill a class of `H¹` are upward closed.** At the level of the
twisted graded module, multiplying by `s^j` the result of multiplying by `sⁿ` is multiplying by
`s^{j + n}`, and `s^j` kills zero. -/
public theorem cohomologyOverFieldMap_twistHom_eq_zero_of_le (F : X.Modules) {n m : ℕ}
    (hnm : n ≤ m) (ξ : (cohomologyOverField k f F 1 : Type u))
    (h : cohomologyOverFieldMap k f (twistHom X L s F n) 1 ξ = 0) :
    cohomologyOverFieldMap k f (twistHom X L s F m) 1 ξ = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + n := ⟨m - n, by omega⟩
  rw [cohomologyOverFieldMap_twistHom_eq_zero_iff] at h ⊢
  rw [← Stacks.Cohomology.TwistedLocalizationMap.actPow_mulPow X L s F 1 ⊤ j n, h,
    Stacks.Cohomology.TwistedLocalizationMap.actPow_zero]

/-- **The third paragraph of [Stacks, Tag 0B5X].** On a proper curve over a field, if the
nonvanishing open of a global section `s` of an invertible module `ℒ` is nonempty and affine,
then every coherent quasi-coherent module `ℱ` has `H¹(X, ℱ ⊗ ℒ^{⊗ N}) = 0` for some `N ≥ 1`.

Every class of the finite-dimensional `H¹(X, ℱ)` is killed by a power of `s`
([Stacks, Tag 01XR]); a finite spanning set is killed by one common power `N`, so multiplication
by `s^N` is the zero map on `H¹(X, ℱ)` while being onto `H¹(X, ℱ ⊗ ℒ^{⊗ N})`. -/
public theorem exists_isZero_cohomologyOverField_one_twist [IsProper f]
    [IrreducibleSpace (X : Type u)] [QuasiSeparatedSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (hU : IsAffineOpen (nonvanishingOpen L s))
    (hne : (↑(nonvanishingOpen L s) : Set X).Nonempty)
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F)
    (hFqc : _root_.SheafOfModules.IsQuasicoherent F) :
    ∃ N : ℕ, 1 ≤ N ∧ IsZero (cohomologyOverField k f (twist X L F (N : ℤ)) 1) := by
  classical
  have _ := hFqc
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have _ : FiniteDimensional k (cohomologyOverField k f F 1) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper k f F hF 1
  have hkill : ∀ ξ : (cohomologyOverField k f F 1 : Type u),
      ∃ n : ℕ, cohomologyOverFieldMap k f (twistHom X L s F n) 1 ξ = 0 := by
    intro ξ
    obtain ⟨n, hn⟩ :=
      Stacks.SheafOfModules.exists_mulPow_eq_zero_of_isAffineOpen_nonvanishingOpen X L s F hU 1
        Nat.one_pos (cohomologyOverFieldAddEquivHgroup k f F 1 ξ)
    exact ⟨n, (cohomologyOverFieldMap_twistHom_eq_zero_iff k f L s F n ξ).mpr hn⟩
  obtain ⟨S, hS⟩ :=
    (inferInstance : Module.Finite k (cohomologyOverField k f F 1 : Type u)).fg_top
  obtain ⟨N, hN, hzero⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : (cohomologyOverField k f F 1 : Type u),
      cohomologyOverFieldMap k f (twistHom X L s F N) 1 ξ = 0 := by
    refine ⟨max (S.sup fun v => (hkill v).choose) 1, le_max_right _ _, fun ξ => ?_⟩
    have hle : (⊤ : Submodule k (cohomologyOverField k f F 1 : Type u)) ≤
        LinearMap.ker (ModuleCat.Hom.hom (cohomologyOverFieldMap k f
          (twistHom X L s F (max (S.sup fun v => (hkill v).choose) 1)) 1)) := by
      rw [← hS]
      refine Submodule.span_le.mpr fun v hv => ?_
      exact cohomologyOverFieldMap_twistHom_eq_zero_of_le k f L s F
        (le_trans (Finset.le_sup (Finset.mem_coe.mp hv)) (le_max_left _ _)) v
        (hkill v).choose_spec
    exact hle Submodule.mem_top
  refine ⟨N, hN, ?_⟩
  have hsurj := surjective_cohomologyOverFieldMap_one_twistHom k f L s hdim hne F hF N
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  rw [← hx, ← hy, hzero, hzero]

end Section

end AlgebraicGeometry

end
