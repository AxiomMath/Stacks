module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.Padics.RingHoms
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Basic
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
public import StacksFrontier.CategoryTheory.Trace.Sorites.Multiplicativity
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.Perfect
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness

/-!
# The ℓ-adic limit of a tower of perfect complexes

Suppose given, for every `n`, a perfect object `Kₙ` of the derived category of
`ℤ/ℓⁿ⁺¹ℤ`-modules, an endomorphism `πₙ` of `Kₙ`, and an isomorphism
`φₙ : Kₙ₊₁ ⊗ᴸ_{ℤ/ℓⁿ⁺²ℤ} ℤ/ℓⁿ⁺¹ℤ ≅ Kₙ` compatible with `πₙ₊₁` and `πₙ`.  Then the traces
`tₙ = Tr(πₙ | Kₙ) ∈ ℤ/ℓⁿ⁺¹ℤ` are compatible and assemble into an element `t_∞ ∈ ℤ_[ℓ]`;
each `Hⁱ_∞ = limₙ Hⁱ(Kₙ)` is a finite `ℤ_[ℓ]`-module, nonzero for finitely many `i` only; and
the endomorphisms `Hⁱ(πₙ)` are compatible with the transitions, so define `πⁱ_∞` on `Hⁱ_∞`,
with `∑ᵢ (-1)ⁱ Tr(πⁱ_∞ | Hⁱ_∞ ⊗_{ℤ_[ℓ]} ℚ_[ℓ]) = t_∞`.

## Main definitions

* `Stacks.InverseSystem.PerfectTower`: the data of the source, i.e. the tower `(Kₙ, πₙ, φₙ)`.
* `Stacks.InverseSystem.traceAtLevel`: the trace `tₙ ∈ ℤ/ℓⁿ⁺¹ℤ` of `πₙ` on the perfect
  object `Kₙ`.
* `Stacks.InverseSystem.padicTrace`: the element `t_∞ ∈ ℤ_[ℓ]` produced by part (1).
* `Stacks.InverseSystem.levelCohomology` and
  `Stacks.InverseSystem.levelCohomologyTransition`: the inverse system `Hⁱ(Kₙ)`, with the
  transition canonically induced by `φₙ`.
* `Stacks.InverseSystem.limitCohomology`: the `ℤ_[ℓ]`-module `Hⁱ_∞ = limₙ Hⁱ(Kₙ)`.
* `Stacks.InverseSystem.limitCohomologyEndo`: the endomorphism `πⁱ_∞` of `Hⁱ_∞`.

## Main results

* `Stacks.InverseSystem.traceAtLevel_compatible` and
  `Stacks.InverseSystem.exists_unique_padicTrace`: part (1), the traces of the tower are
  compatible and assemble into a unique `t_∞ ∈ ℤ_[ℓ]`.
* `Stacks.InverseSystem.finite_limitCohomology` and
  `Stacks.InverseSystem.finite_setOf_nontrivial_limitCohomology`: part (2), each `Hⁱ_∞` is a
  finite `ℤ_[ℓ]`-module and `Hⁱ_∞` vanishes for all but finitely many `i`.
* `Stacks.InverseSystem.levelCohomologyEndoHom_transition` and
  `Stacks.InverseSystem.limitCohomologyEndo`: the `Hⁱ(πₙ)` are compatible with the transitions
  and so define `πⁱ_∞` on `Hⁱ_∞`.
* `Stacks.InverseSystem.alternating_trace_eq_padicTrace`: part (3), the alternating sum of the
  traces of `πⁱ_∞` on `Hⁱ_∞ ⊗_{ℤ_[ℓ]} ℚ_[ℓ]` is `t_∞`.
* `Stacks.InverseSystem.perfectTower_padicTrace_eq_alternating_trace_limitCohomology`: the whole
  lemma, parts (1), (2) and (3) together, under the hypotheses of the source and nothing more.
  This is the declaration carrying the tag; the results above are its components.

## Implementation notes

Levels are indexed by `n : ℕ`, level `n` carrying coefficients in `ℤ/ℓⁿ⁺¹ℤ`; this avoids the
degenerate zero ring.

The source presents the comparison as an isomorphism `φₙ` out of the derived base change of
`Kₙ₊₁`.  Taking that at face value leaves the induced map `Hⁱ(Kₙ₊₁) → Hⁱ(Kₙ)` — which parts (2)
and (3) quantify over — undefined, because it also needs the unit of derived base change.
So `PerfectTower` records instead the *adjoint transpose* `tₙ : Kₙ₊₁ ⟶ Res(Kₙ)` of `φₙ`, in the
derived category of the larger ring, together with the requirement that the morphism it
transposes to be an isomorphism.  Transposition along `derivedExtensionScalarsAdjunction` is a
bijection, and carries the source's compatibility of `φₙ` with `πₙ₊₁, πₙ` to the stated
compatibility of `tₙ`, so this is the same data.  With `tₙ` in hand the cohomology transition is
canonical: `Hⁱ(tₙ)` followed by the comparison identifying the cohomology of a restriction of
scalars with the restriction of scalars of the cohomology (restriction of scalars is exact), the
comparison being the unique lift along the localization `DerivedCategory.Q`.

Derived base change is the model `totalDerivedExtensionScalars`; a different model is identified
with it by the uniqueness of left derived functors, so which one is used affects neither the
transpose condition nor anything downstream.

`ℤ_[ℓ]` acts on level `n` through `PadicInt.toZModPow (n + 1)` and `Hⁱ_∞` is the submodule of
compatible families inside the product.  Mathlib's `ℤ_[ℓ]` is not literally an inverse limit, so
"the `tₙ` form an element of `ℤ_[ℓ]`" is stated as the existence of a unique `t_∞` reducing to
every `tₙ`.

The trace `FilteredDerived.perfectDerivedTrace` is valued in the additive commutator quotient of
the coefficient ring; `commutativeAdditiveCommutatorQuotientEval` gives its canonical evaluation
in a commutative ring.

## References

* [Stacks Project, Tag 03V4](https://stacks.math.columbia.edu/tag/03V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Trace
open scoped BigOperators TensorProduct

universe u w v

namespace Stacks.InverseSystem

open CategoryTheory.FilteredDerived (finite_nonzero_degrees)

attribute [local instance] HasDerivedCategory.standard

/-! ### The coefficient tower -/

/-- The reduction `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ` of coefficient rings. -/
public abbrev levelCast (ℓ n : ℕ) : ZMod (ℓ ^ (n + 1 + 1)) →+* ZMod (ℓ ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow ℓ (by omega : n + 1 ≤ n + 1 + 1)) _

/-- Restriction of scalars along `levelCast`, on derived categories of modules. -/
public abbrev levelRestrict (ℓ n : ℕ) :
    DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) ⥤
      DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) :=
  (ModuleCat.restrictScalars.{v} (levelCast ℓ n)).mapDerivedCategory

/-- A choice of total derived extension of scalars along `levelCast`. -/
public abbrev levelExtensionData (ℓ n : ℕ) :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, v} (levelCast ℓ n)

/-- Derived base change `- ⊗ᴸ_{ℤ/ℓⁿ⁺²ℤ} ℤ/ℓⁿ⁺¹ℤ`. -/
public abbrev levelBaseChange (ℓ n : ℕ) :
    DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ (n + 1 + 1)))) ⥤
      DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ (n + 1)))) :=
  (levelExtensionData.{v} ℓ n).functor

/-- Derived base change is left adjoint to restriction of scalars. -/
public def levelAdjunction (ℓ n : ℕ) : levelBaseChange.{v} ℓ n ⊣ levelRestrict.{v} ℓ n := by
  let D := levelExtensionData.{v} ℓ n
  letI := D.isLeftDerived
  exact @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{0, 0, v}
    _ _ _ _ (levelCast ℓ n) _ _ D.functor D.comparison D.isLeftDerived

/-- Restriction of scalars along a ring homomorphism is exact, so the cohomology of a
restriction of scalars is the restriction of scalars of the cohomology.  This is the
comparison that makes the cohomology transition of a tower canonical; it is the unique
natural isomorphism lifting the corresponding isomorphism of functors on cochain complexes
along the localization `DerivedCategory.Q`. -/
public def restrictHomologyIsoOfHom {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (i : ℤ) :
    (ModuleCat.restrictScalars.{v} f).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} R) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{v} S) i ⋙
        ModuleCat.restrictScalars.{v} f := by
  let F := ModuleCat.restrictScalars.{v} f
  let C₁ := ModuleCat.{v} S
  let C₂ := ModuleCat.{v} R
  letI liftA : Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) i)
      (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ i) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors C₂ i)⟩
  letI liftB : Localization.Lifting (DerivedCategory.Q)
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) i ⋙ F)
      (DerivedCategory.homologyFunctor C₁ i ⋙ F) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ i) F⟩
  let hcComm :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) i ≅
        HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) i ⋙ F :=
    Functor.isoWhiskerLeft _ (HomologicalComplex.homologyFunctorIso C₂ (ComplexShape.up ℤ) i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.shortComplexFunctor C₂ (ComplexShape.up ℤ) i))
      (ShortComplex.homologyFunctor C₂) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) i)
      (ShortComplex.homologyFunctorIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.homologyFunctorIso C₁ (ComplexShape.up ℤ) i).symm F
  exact Localization.liftNatIso (DerivedCategory.Q)
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) i)
    (HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) i ⋙ F)
    _ _ hcComm

/-! ### The tower -/

/-- **Stacks 03V4.** A tower of perfect complexes over the rings `ℤ/ℓⁿ⁺¹ℤ`: perfect objects
`Kₙ` of `D(ℤ/ℓⁿ⁺¹ℤ)`, endomorphisms `πₙ` of `Kₙ`, and comparisons identifying the derived base
change of `Kₙ₊₁` with `Kₙ` compatibly with the endomorphisms.

A comparison is recorded as its adjoint transpose `transition n : Kₙ₊₁ ⟶ Res Kₙ`, the
requirement being that the morphism `baseChange Kₙ₊₁ ⟶ Kₙ` it transposes to — the source's
`φₙ` — is an isomorphism. -/
public structure PerfectTower (ℓ : ℕ) where
  /-- The object `Kₙ` of `D(ℤ/ℓⁿ⁺¹ℤ)`. -/
  obj : (n : ℕ) → DerivedCategory (ModuleCat.{v} (ZMod (ℓ ^ (n + 1))))
  /-- Every `Kₙ` is perfect. -/
  isPerfect : ∀ n, StacksDraft.Perfect.IsPerfect (obj n)
  /-- The endomorphism `πₙ` of `Kₙ`. -/
  endo : ∀ n, obj n ⟶ obj n
  /-- The adjoint transpose of the comparison `φₙ`. -/
  transition : ∀ n, obj (n + 1) ⟶ (levelRestrict.{v} ℓ n).obj (obj n)
  /-- The comparison `φₙ : Kₙ₊₁ ⊗ᴸ ℤ/ℓⁿ⁺¹ℤ ⟶ Kₙ` is an isomorphism. -/
  comparison_isIso : ∀ n, IsIso (((levelAdjunction.{v} ℓ n).homEquiv _ _).symm (transition n))
  /-- The comparison is compatible with `πₙ₊₁` and `πₙ`. -/
  endo_compatible : ∀ n, endo (n + 1) ≫ transition n =
    transition n ≫ (levelRestrict.{v} ℓ n).map (endo n)

/-- The perfect object `Kₙ` regarded as an object of `D_perf(ℤ/ℓⁿ⁺¹ℤ)`. -/
public abbrev PerfectTower.perfectObj {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (n : ℕ) :
    FilteredDerived.PerfectDerivedCategory.{0, v} (ZMod (ℓ ^ (n + 1))) :=
  ⟨T.obj n, T.isPerfect n⟩

/-! ### Part (1): the traces assemble into an ℓ-adic integer -/

/-- The trace `tₙ = Tr(πₙ | Kₙ) ∈ ℤ/ℓⁿ⁺¹ℤ`. -/
public def traceAtLevel {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (n : ℕ) : ZMod (ℓ ^ (n + 1)) :=
  commutativeAdditiveCommutatorQuotientEval _
    (FilteredDerived.perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) (T.perfectObj n) (T.endo n))

private lemma commutatorQuotientEval_mk {R : Type u} [CommRing R] (x : R) :
    commutativeAdditiveCommutatorQuotientEval R
      (FilteredDerived.additiveCommutatorQuotientMk R x) = x := by
  simp [commutativeAdditiveCommutatorQuotientEval,
    FilteredDerived.additiveCommutatorQuotientMk]

private lemma freeModuleTrace_eval {R : Type u} [CommRing R]
    (ι : Type v) [Fintype ι] (f : Module.End R (ι → R)) :
    commutativeAdditiveCommutatorQuotientEval R
      (FilteredDerived.freeModuleTrace R ι f) = LinearMap.trace R (ι → R) f := by
  classical
  rw [FilteredDerived.freeModuleTrace_apply, commutatorQuotientEval_mk]
  rw [LinearMap.trace_eq_matrix_trace R (Pi.basisFun R ι)]
  simp [Matrix.trace, FilteredDerived.standardBasisVector]

private lemma projectiveTrace_eval_eq_trace_of_split {R : Type u} [CommRing R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) (F : Type w) [AddCommGroup F] [Module R F]
    [Module.Free R F] [Module.Finite R F]
    (p : F →ₗ[R] P) (i : P →ₗ[R] F) (hi : p.comp i = LinearMap.id) :
    commutativeAdditiveCommutatorQuotientEval R
      (projectiveModuleTrace R P f) = LinearMap.trace R F (i.comp (f.comp p)) := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := h.choose
  let p₀ : (Fin n → R) →ₗ[R] P := h.choose_spec.choose
  let i₀ : P →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  have hi₀ : p₀.comp i₀ = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  let a : F →ₗ[R] (Fin n → R) := i₀.comp p
  let b : (Fin n → R) →ₗ[R] F := i.comp (f.comp p₀)
  have hi_apply (x : P) : p (i x) = x := by
    simpa using congrFun (congrArg DFunLike.coe hi) x
  have hi₀_apply (x : P) : p₀ (i₀ x) = x := by
    simpa using congrFun (congrArg DFunLike.coe hi₀) x
  have hab : b.comp a = i.comp (f.comp p) := by
    ext x
    simp only [LinearMap.comp_apply, a, b]
    rw [hi₀_apply (p x)]
  have hba : a.comp b = i₀.comp (f.comp p₀) := by
    ext x
    simp only [LinearMap.comp_apply, a, b]
    rw [hi_apply]
  show commutativeAdditiveCommutatorQuotientEval R
    (FilteredDerived.freeModuleTrace R (Fin n) (i₀.comp (f.comp p₀))) = _
  rw [freeModuleTrace_eval]
  rw [← hba, ← hab]
  exact LinearMap.trace_comp_comm' b a

private lemma projectiveTrace_eval_baseChange {R : Type u} [CommRing R]
    {S : Type w} [CommRing S] [Algebra R S]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (f : Module.End R P) :
    commutativeAdditiveCommutatorQuotientEval S
        (projectiveModuleTrace S (S ⊗[R] P) (LinearMap.baseChange S f)) =
      algebraMap R S
        (commutativeAdditiveCommutatorQuotientEval R
          (projectiveModuleTrace R P f)) := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := h.choose
  let p : (Fin n → R) →ₗ[R] P := h.choose_spec.choose
  let i : P →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  have hi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  let F := S ⊗[R] (Fin n → R)
  let : Module.Free S F :=
    Module.Free.of_basis (Algebra.TensorProduct.basis S (Pi.basisFun R (Fin n)))
  let : Module.Finite S F :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Pi.basisFun R (Fin n)))
  let pS : F →ₗ[S] S ⊗[R] P := LinearMap.baseChange S p
  let iS : S ⊗[R] P →ₗ[S] F := LinearMap.baseChange S i
  have hiS : pS.comp iS = LinearMap.id := by
    rw [← LinearMap.baseChange_comp (A := S) i p, hi, LinearMap.baseChange_id]
  have hR := projectiveTrace_eval_eq_trace_of_split (R := R) P f (Fin n → R) p i hi
  have hS := projectiveTrace_eval_eq_trace_of_split (R := S) (S ⊗[R] P)
    (LinearMap.baseChange S f) F pS iS hiS
  rw [hS, hR]
  have hcomp : iS.comp ((LinearMap.baseChange S f).comp pS) =
      LinearMap.baseChange S (i.comp (f.comp p)) := by
    rw [← LinearMap.baseChange_comp (A := S) p f,
      ← LinearMap.baseChange_comp (A := S) (f.comp p) i]
  rw [hcomp, LinearMap.trace_baseChange]

private theorem projective_extendScalars {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : ModuleCat.{v} R) (hP : Projective P) :
    Projective ((ModuleCat.extendScalars.{0,0,v} φ).obj P) := by
  let : (ModuleCat.restrictScalars.{v,0,0} φ).PreservesEpimorphisms := ⟨fun f hf => by
    apply (ModuleCat.epi_iff_surjective _).2
    exact (ModuleCat.epi_iff_surjective f).mp hf⟩
  exact (ModuleCat.extendRestrictScalarsAdj.{v,0,0} φ).map_projective P hP

private theorem finite_extendScalars {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : ModuleCat.{v} R) (hP : Module.Finite R P) :
    Module.Finite S ((ModuleCat.extendScalars.{0,0,v} φ).obj P) := by
  let : Module.Finite R P := hP
  let : Algebra R S := φ.toAlgebra
  have heq : (inferInstance : Module R S) = Module.compHom S φ :=
    Module.ext' _ _ (by intro r s; rfl)
  cases heq
  exact Module.Finite.base_change R S P

private theorem finiteProjectiveComplex_extendScalars {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : FilteredDerived.finiteProjectiveComplex R P) :
    FilteredDerived.finiteProjectiveComplex S
      (((ModuleCat.extendScalars.{0,0,v} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  let E := ModuleCat.extendScalars.{0,0,v} φ
  let : Algebra R S := φ.toAlgebra
  constructor
  · refine ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := hP.1.1
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact Functor.map_isZero E (P.isZero_of_isStrictlyGE n i hi)
    · obtain ⟨n, hn⟩ := hP.1.2
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact Functor.map_isZero E (P.isZero_of_isStrictlyLE n i hi)
  · intro i
    let : Module.Projective R (P.X i) := (hP.2 i).1
    let : Module.Finite R (P.X i) := (hP.2 i).2
    constructor
    · have hp : Projective (E.obj (P.X i)) :=
        projective_extendScalars φ (P.X i)
          ((IsProjective.iff_projective (R := R) (P := P.X i)).mp inferInstance)
      exact (IsProjective.iff_projective (R := S) (P := E.obj (P.X i))).mpr hp
    · exact finite_extendScalars φ (P.X i) (hP.2 i).2


private lemma projectiveTrace_zero_of_subsingleton {R : Type} [Ring R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    [Subsingleton M] (f : Module.End R M) : projectiveModuleTrace R M f = 0 := by
  have hf : f = 0 := by ext x; exact Subsingleton.elim _ _
  rw [hf]
  simp [projectiveModuleTrace]


private theorem alternatingTrace_eval_baseChange {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : FilteredDerived.finiteProjectiveComplex R P) (g : P ⟶ P) :
    commutativeAdditiveCommutatorQuotientEval S
      (FilteredDerived.alternatingTrace S
        (((ModuleCat.extendScalars.{0,0,v} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (finiteProjectiveComplex_extendScalars φ P hP)
        (((ModuleCat.extendScalars.{0,0,v} φ).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) =
      φ
        (commutativeAdditiveCommutatorQuotientEval R
          (FilteredDerived.alternatingTrace R P hP g)) := by
  classical
  let E := ModuleCat.extendScalars.{0,0,v} φ
  let : Algebra R S := φ.toAlgebra
  let P' := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let hP' := finiteProjectiveComplex_extendScalars φ P hP
  let g' := (E.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  let t : ∀ (A : Type) [CommRing A] (Q : CochainComplex (ModuleCat.{v} A) ℤ),
      FilteredDerived.finiteProjectiveComplex A Q → (Q ⟶ Q) →
        ℤ → FilteredDerived.AdditiveCommutatorQuotient A := fun A _ Q hQ g' i => by
    let : Module.Projective A (Q.X i) := (hQ.2 i).1
    let : Module.Finite A (Q.X i) := (hQ.2 i).2
    exact if Even i then projectiveModuleTrace A (Q.X i) (g'.f i).hom
      else -projectiveModuleTrace A (Q.X i) (g'.f i).hom
  have hfinite : ∀ (A : Type) [CommRing A] (Q : CochainComplex (ModuleCat.{v} A) ℤ)
      (hQ : FilteredDerived.finiteProjectiveComplex A Q) (g' : Q ⟶ Q),
      Function.HasFiniteSupport (t A Q hQ g') := by
    intro A _ Q hQ g'
    apply (finite_nonzero_degrees _ Q hQ).subset
    intro i hi
    change t A Q hQ g' i ≠ 0 at hi
    by_contra hz
    have hzero : IsZero (Q.X i) := not_not.mp hz
    let : Module.Projective A (Q.X i) := (hQ.2 i).1
    let : Module.Finite A (Q.X i) := (hQ.2 i).2
    have : Subsingleton (Q.X i) := ModuleCat.subsingleton_of_isZero hzero
    have ht := projectiveTrace_zero_of_subsingleton (Q.X i) (g'.f i).hom
    simp [t, ht] at hi
  let tR := t R P hP g
  let tS := t S P' hP' g'
  have hfiniteR : Function.HasFiniteSupport tR := hfinite R P hP g
  have hfiniteS : Function.HasFiniteSupport tS := hfinite S P' hP' g'
  let evR := commutativeAdditiveCommutatorQuotientEval R
  let evS := commutativeAdditiveCommutatorQuotientEval S
  have hmR := AddMonoidHom.map_finsum evR hfiniteR
  have hmS := AddMonoidHom.map_finsum evS hfiniteS
  have hfiniteEv : Function.HasFiniteSupport (evR ∘ tR) := by
    apply hfiniteR.subset
    intro i hi
    simp only [Function.mem_support, Function.comp_apply] at hi ⊢
    by_contra hzero
    apply hi
    simp [hzero]
  have hmφ := AddMonoidHom.map_finsum φ.toAddMonoidHom hfiniteEv
  show evS (FilteredDerived.alternatingTrace S P' hP' g') =
    φ (evR (FilteredDerived.alternatingTrace R P hP g))
  unfold FilteredDerived.alternatingTrace
  show evS (∑ᶠ i, tS i) = φ (evR (∑ᶠ i, tR i))
  rw [hmS, hmR]
  show (∑ᶠ i, evS (tS i)) = φ.toAddMonoidHom (∑ᶠ i, (evR ∘ tR) i)
  rw [hmφ]
  apply finsum_congr
  intro i
  simp only [tR, tS, t, Function.comp_apply]
  let : Module.Projective R (P.X i) := (hP.2 i).1
  let : Module.Finite R (P.X i) := (hP.2 i).2
  let : Algebra R S := φ.toAlgebra
  let : Module.Projective S (P'.X i) := (hP'.2 i).1
  let : Module.Finite S (P'.X i) := (hP'.2 i).2
  have hg : (g'.f i).hom = LinearMap.baseChange S (g.f i).hom := rfl
  by_cases hi : Even i
  · simp only [hi, ite_true]
    rw [hg]
    exact projectiveTrace_eval_baseChange (R := R) (S := S) (P.X i) (g.f i).hom
  · simp only [hi, ite_false, map_neg]
    rw [hg]
    exact congrArg Neg.neg
      (projectiveTrace_eval_baseChange (R := R) (S := S) (P.X i) (g.f i).hom)

private lemma baseChange_endo_compatible {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (n : ℕ) :
    (levelBaseChange.{v} ℓ n).map (T.endo (n + 1)) ≫
        ((levelAdjunction.{v} ℓ n).homEquiv _ _).symm (T.transition n) =
      ((levelAdjunction.{v} ℓ n).homEquiv _ _).symm (T.transition n) ≫ T.endo n := by
  let adj := levelAdjunction.{v} ℓ n
  let φ := (adj.homEquiv (T.obj (n + 1)) (T.obj n)).symm (T.transition n)
  have hφ : adj.homEquiv (T.obj (n + 1)) (T.obj n) φ = T.transition n :=
    Equiv.apply_symm_apply _ _
  apply (adj.homEquiv (T.obj (n + 1)) (T.obj n)).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rw [hφ]
  exact T.endo_compatible n

lemma exists_cochainEndo {S : Type} [Ring S]
    (P : CochainComplex (ModuleCat.{v} S) ℤ) (hP : FilteredDerived.finiteProjectiveComplex S P)
    (K : DerivedCategory (ModuleCat.{v} S)) (e : DerivedCategory.Q.obj P ≅ K) (f : K ⟶ K) :
    ∃ g : P ⟶ P, DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv := by
  obtain ⟨upper, hupper⟩ := hP.1.2
  let : P.IsStrictlyLE upper := hupper
  let (i : ℤ) : Module.Projective S (P.X i) := (hP.2 i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  let : CochainComplex.IsKProjective P :=
    CochainComplex.isKProjective_of_projective P upper
  let Q := HomotopyCategory.quotient (ModuleCat.{v} S) (ComplexShape.up ℤ)
  let q := Q.obj P
  let qIso := DerivedCategory.quotientCompQhIso (ModuleCat.{v} S)
  let α : DerivedCategory.Qh.obj q ≅ K := qIso.app P ≪≫ e
  let gH : q ⟶ q :=
    (CochainComplex.IsKProjective.Qh_map_bijective P q).surjective
      (α.hom ≫ f ≫ α.inv) |>.choose
  have hgH : (DerivedCategory.Qh).map gH = α.hom ≫ f ≫ α.inv :=
    (CochainComplex.IsKProjective.Qh_map_bijective P q).surjective
      (α.hom ≫ f ≫ α.inv) |>.choose_spec
  let g : P ⟶ P := Q.preimage gH
  have hgQ : Q.map g = gH := by simp [g]
  have hq : qIso.inv.app P ≫ (DerivedCategory.Qh).map (Q.map g) ≫ qIso.hom.app P =
      DerivedCategory.Q.map g := by
    have hn : DerivedCategory.Q.map g ≫ qIso.inv.app P =
        qIso.inv.app P ≫ (DerivedCategory.Qh).map (Q.map g) := by
      simp [Q, qIso]
    calc
      _ = (qIso.inv.app P ≫ (DerivedCategory.Qh).map (Q.map g)) ≫
            qIso.hom.app P := by simp only [Category.assoc]
      _ = (DerivedCategory.Q.map g ≫ qIso.inv.app P) ≫ qIso.hom.app P := by rw [hn.symm]
      _ = DerivedCategory.Q.map g := by simp [Category.assoc, qIso]
  have hg : DerivedCategory.Q.map g = e.hom ≫ f ≫ e.inv := by
    calc
      DerivedCategory.Q.map g = qIso.inv.app P ≫
          (DerivedCategory.Qh).map (Q.map g) ≫ qIso.hom.app P := hq.symm
      _ = e.hom ≫ f ≫ e.inv := by
        rw [hgQ, hgH]
        simp [α, Category.assoc]
  exact ⟨g, hg⟩

private lemma perfectTrace_baseChange {S R : Type} [CommRing S] [CommRing R]
    (φ : S →+* R) (M : FilteredDerived.PerfectDerivedCategory.{0, v} S)
    (N : FilteredDerived.PerfectDerivedCategory.{0, v} R)
    (a : M.obj ⟶ M.obj) (b : N.obj ⟶ N.obj)
    (β₀ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, v}
      φ).functor.obj M.obj ⟶ N.obj) [IsIso β₀]
    (hβ₀ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, v}
      φ).functor.map a ≫ β₀ = β₀ ≫ b) :
    φ (commutativeAdditiveCommutatorQuotientEval S
      (FilteredDerived.perfectDerivedTrace S M a)) =
      commutativeAdditiveCommutatorQuotientEval R
        (FilteredDerived.perfectDerivedTrace R N b) := by
  classical
  let K := M.obj
  let f := a
  let h := (FilteredDerived.isPerfect_iff S K).mp (M.property)
  let P := h.choose
  let hP : FilteredDerived.finiteProjectiveComplex S P := h.choose_spec.1
  let e : DerivedCategory.Q.obj P ≅ K := h.choose_spec.2.some
  obtain ⟨upper, hupper⟩ := hP.1.2
  let : P.IsStrictlyLE upper := hupper
  let (i : ℤ) : Module.Projective S (P.X i) := (hP.2 i).1
  let (i : ℤ) : Projective (P.X i) := inferInstance
  obtain ⟨g, hg⟩ := exists_cochainEndo P hP K e f
  have htraceHigh :
      commutativeAdditiveCommutatorQuotientEval S
          (FilteredDerived.perfectDerivedTrace S (M) f) =
        commutativeAdditiveCommutatorQuotientEval S
          (FilteredDerived.alternatingTrace S P hP g) := by
    rw [FilteredDerived.perfectDerivedTrace_eq_alternatingTrace S
      (M) f P hP e g hg]
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{0, 0, v} φ
  let E := ModuleCat.extendScalars.{0,0,v} φ
  let F := (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q
  let P' := (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let hP' := finiteProjectiveComplex_extendScalars φ P hP
  let g' := (E.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  have hcatProj : ∀ i : ℤ, Projective (P.X i) := fun i => by
    let : Module.Projective S (P.X i) := (hP.2 i).1
    exact (IsProjective.iff_projective (R := S) (P := P.X i)).mp inferInstance
  let : ∀ i : ℤ, Projective (P.X i) := hcatProj
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P upper
  let c : D.functor.obj (DerivedCategory.Q.obj P) ≅ F.obj P :=
    @asIso _ _ _ _ (D.comparison.app P) hcomp
  have hMapIso : IsIso (D.functor.map e.inv) := by infer_instance
  let θ : D.functor.obj K ≅ F.obj P :=
    (@asIso _ _ _ _ (D.functor.map e.inv) hMapIso) ≪≫ c
  let β : D.functor.obj K ⟶ N.obj :=
    β₀
  have hβiso : IsIso β := inferInstance
  let βIso : D.functor.obj K ≅ N.obj := @asIso _ _ _ _ β hβiso
  let α' : DerivedCategory.Q.obj P' ≅ N.obj := by
    show F.obj P ≅ N.obj
    exact θ.symm ≪≫ βIso
  have : IsIso (D.comparison.app P) := hcomp
  have : IsIso (D.functor.map e.inv) := hMapIso
  have hc_hom : c.hom = D.comparison.app P := by
    show (@asIso _ _ _ _ (D.comparison.app P) hcomp).hom = D.comparison.app P
    rfl
  have hθhom : θ.hom = D.functor.map e.inv ≫ D.comparison.app P := rfl
  have hconj : f ≫ e.inv = e.inv ≫ DerivedCategory.Q.map g := by
    rw [hg]
    simp
  have hmap : F.map g = DerivedCategory.Q.map g' := by
    rfl
  have hθ₀ : D.functor.map f ≫ (D.functor.map e.inv ≫ D.comparison.app P) =
      (D.functor.map e.inv ≫ D.comparison.app P) ≫ F.map g := by
    have hnat : D.functor.map (DerivedCategory.Q.map g) ≫ D.comparison.app P =
        D.comparison.app P ≫ F.map g := by
      simpa [F, D, E,
        CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral,
        CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex] using
        (D.comparison.naturality g)
    rw [← Category.assoc, ← D.functor.map_comp f e.inv, hconj,
      D.functor.map_comp e.inv (DerivedCategory.Q.map g), Category.assoc, hnat]
    exact (Category.assoc (D.functor.map e.inv) (D.comparison.app P) (F.map g)).symm
  have hθ : D.functor.map f ≫ θ.hom = θ.hom ≫ F.map g := by
    rw [hθhom]
    exact hθ₀
  have hθ' : F.map g ≫ θ.inv = θ.inv ≫ D.functor.map f := by
    have h := congrArg (fun z => θ.inv ≫ z ≫ θ.inv) hθ
    simpa [Category.assoc] using h.symm
  have hβ' : D.functor.map f ≫ β = β ≫ b := by
    exact hβ₀
  have : IsIso β := hβiso
  have hα'₀ : F.map g ≫ θ.inv ≫ β = θ.inv ≫ β ≫ b := by
    calc
      F.map g ≫ θ.inv ≫ β = (F.map g ≫ θ.inv) ≫ β := by rw [← Category.assoc]
      _ = (θ.inv ≫ D.functor.map f) ≫ β := by rw [hθ']
      _ = θ.inv ≫ (D.functor.map f ≫ β) := by rw [Category.assoc]
      _ = θ.inv ≫ (β ≫ b) := by rw [hβ']
      _ = θ.inv ≫ β ≫ b := rfl
  have hβhom : βIso.hom = β := by
    let : IsIso β := hβiso
    exact asIso_hom _
  have hα' : DerivedCategory.Q.map g' ≫ α'.hom = α'.hom ≫ b := by
    have hhom : α'.hom = θ.inv ≫ β := by
      show (θ.symm ≪≫ βIso).hom = θ.inv ≫ β
      simp only [Iso.trans_hom, Iso.symm_hom, hβhom]
    rw [hhom]
    rw [← hmap]
    simpa [Category.assoc] using hα'₀
  have hαF : F.map g ≫ α'.hom = α'.hom ≫ b := by
    rw [hmap]
    exact hα'
  have hg' : DerivedCategory.Q.map g' = α'.hom ≫ b ≫ α'.inv := by
    calc
      DerivedCategory.Q.map g' = F.map g := hmap.symm
      _ = (F.map g ≫ α'.hom) ≫ α'.inv := by simp
      _ = (α'.hom ≫ b) ≫ α'.inv := by rw [hαF]
      _ = α'.hom ≫ b ≫ α'.inv := by simp [Category.assoc]
  have htraceLow :
      commutativeAdditiveCommutatorQuotientEval R
          (FilteredDerived.perfectDerivedTrace R (N) (b)) =
        commutativeAdditiveCommutatorQuotientEval R
          (FilteredDerived.alternatingTrace R P' hP' g') := by
    rw [FilteredDerived.perfectDerivedTrace_eq_alternatingTrace R
      (N) (b) P' hP' α' g' hg']
  show φ (commutativeAdditiveCommutatorQuotientEval S
      (FilteredDerived.perfectDerivedTrace S (M) f)) =
    commutativeAdditiveCommutatorQuotientEval R
      (FilteredDerived.perfectDerivedTrace R (N) (b))
  rw [htraceHigh, htraceLow]
  exact (alternatingTrace_eval_baseChange φ P hP g).symm

/-- **Stacks 03V4, part (1).** The traces of the tower are compatible under the reductions of
the coefficient rings. -/
public theorem traceAtLevel_compatible {ℓ : ℕ} (T : PerfectTower.{v} ℓ) (n : ℕ) :
    levelCast ℓ n (traceAtLevel T (n + 1)) = traceAtLevel T n := by
  let := T.comparison_isIso n
  exact perfectTrace_baseChange (levelCast ℓ n) (T.perfectObj (n + 1)) (T.perfectObj n)
    (T.endo (n + 1)) (T.endo n)
    (((levelAdjunction.{v} ℓ n).homEquiv _ _).symm (T.transition n))
    (baseChange_endo_compatible T n)

private lemma traceAtLevel_val_sub_dvd {ℓ : ℕ} [Fact ℓ.Prime]
    (T : PerfectTower.{v} ℓ) (n : ℕ) :
    (ℓ : ℤ) ^ (n + 1) ∣
      ((traceAtLevel T (n + 1)).val : ℤ) - ((traceAtLevel T n).val : ℤ) := by
  have hcast := traceAtLevel_compatible T n
  have hnat :
      ((traceAtLevel T (n + 1)).val : ZMod (ℓ ^ (n + 1))) =
        (traceAtLevel T n).val := by
    rw [← ZMod.natCast_zmod_val (traceAtLevel T (n + 1)),
      ← ZMod.natCast_zmod_val (traceAtLevel T n)] at hcast
    simpa [levelCast, ZMod.castHom_apply] using hcast
  have hh :
      (((traceAtLevel T (n + 1)).val : ℤ) : ZMod (ℓ ^ (n + 1))) =
        ((traceAtLevel T n).val : ℤ) := by
    exact_mod_cast hnat
  obtain ⟨c, hc⟩ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hh
  refine ⟨-c, ?_⟩
  have hneg : ((traceAtLevel T (n + 1)).val : ℤ) - ((traceAtLevel T n).val : ℤ) =
      -(((traceAtLevel T n).val : ℤ) - ((traceAtLevel T (n + 1)).val : ℤ)) := by ring
  rw [hneg, hc]
  push_cast
  ring_nf

/-- **Stacks 03V4, part (1).** The traces `tₙ` form an element `t_∞` of `ℤ_[ℓ]`: there is a
unique ℓ-adic integer whose reduction modulo `ℓⁿ⁺¹` is `tₙ` for every `n`. -/
public theorem exists_unique_padicTrace {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) :
    ∃! t : ℤ_[ℓ], ∀ n : ℕ, PadicInt.toZModPow (n + 1) t = traceAtLevel T n := by
  let seq : ℕ → ℤ := fun n =>
    if n = 0 then 0 else ((traceAtLevel T (n - 1)).val : ℤ)
  have hseq : ∀ i, (ℓ : ℤ) ^ i ∣ seq (i + 1) - seq i := by
    intro i
    cases i with
    | zero =>
        simp [seq]
    | succ i =>
        simpa [seq] using traceAtLevel_val_sub_dvd T i
  let x : ℤ_[ℓ] := PadicInt.ofIntSeq seq
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub seq ℓ hseq)
  refine ⟨x, ?_, ?_⟩
  · intro n
    have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub seq ℓ hseq (n + 1)
    simpa [x, seq] using h
  · intro y hy
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        let : Subsingleton (ZMod (ℓ ^ 0)) := by
          rw [show ℓ ^ 0 = 1 by simp]
          infer_instance
        exact Subsingleton.elim _ _
    | succ n =>
        have hx := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub seq ℓ hseq (n + 1)
        have hx' : PadicInt.toZModPow (n + 1) x = traceAtLevel T n := by
          simpa [x, seq, ZMod.natCast_zmod_val] using hx
        exact (hy n).trans hx'.symm

/-- The element `t_∞ ∈ ℤ_[ℓ]` determined by the traces of the tower. -/
public def padicTrace {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) : ℤ_[ℓ] :=
  (exists_unique_padicTrace T).choose

/-- The reduction of `t_∞` modulo `ℓⁿ⁺¹` is the trace `tₙ` at level `n`. -/
public theorem toZModPow_padicTrace {ℓ : ℕ} [Fact ℓ.Prime] (T : PerfectTower.{v} ℓ) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (padicTrace T) = traceAtLevel T n :=
  (exists_unique_padicTrace T).choose_spec.1 n

end Stacks.InverseSystem

end
