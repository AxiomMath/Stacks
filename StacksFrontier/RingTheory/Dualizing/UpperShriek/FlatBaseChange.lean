module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChangeIsomorphism
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialExtension
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionTensorComparison
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Flat base change for the algebraic upper shriek functor: the ingredients

Let `R → R'` be a flat homomorphism, let `φ : R → A` be of finite type and let
`φ' : R' → A' = R' ⊗_R A` be obtained from `φ` by base change.  Every polynomial presentation
`p` of `φ` base changes to one of `φ'`.  This file provides the ingredients of the flat-base-change
map `φ^!(K) ⊗_A^L A' ⟶ (φ')^!(K ⊗_R^L R')` of [stacks 0BZN]: the base-changed presentation, the
identification of the pushout `A ⊗_P P'` with `R' ⊗_R A`, flatness and Tor independence of the
square of a presentation, and the degreewise model of derived extension of scalars along a flat
homomorphism.  The map itself and its invertibility on `D⁺(R)` are
`Dualizing.PolynomialPresentation.upperShriekFlatBaseChange` and
`Dualizing.PolynomialPresentation.isIso_upperShriekFlatBaseChange_app` in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeIso`, at every module universe.

## Main definitions

* `Dualizing.flatDerivedExtension` — derived extension of scalars along a flat ring
  homomorphism, computed degreewise.
* `Dualizing.PolynomialPresentation.baseChange` — the base change of a polynomial presentation.
* `Dualizing.pushoutEquiv` — the pushout `A ⊗_P P'` of the square of a presentation is
  `R' ⊗_R A`.
* `Dualizing.KFlatAlgebraActionEq` — the projection-formula compatibility of [stacks 0E2A], in
  the reduced form the library's general [stacks 0BZM] takes it, quantified over every square and
  every pair of models of derived extension of scalars.

## Main results

* `Dualizing.torIndependent_of_flat_right` — a flat algebra is Tor independent from every
  algebra.
* `Dualizing.kFlatAlgebraActionEq_of_tensorComparisonCompatibility` — `KFlatAlgebraActionEq`
  from the tensor-comparison obligation.

## References

* [Stacks Project, Tag 0BZN](https://stacks.math.columbia.edu/tag/0BZN)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.DerivedRingEquivIso

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The base change along `R → R'` of a polynomial presentation `P = R[x_1, …, x_n] ↠ A` of
`φ : R → A`: the presentation `P' = R'[x_1, …, x_n] ↠ R' ⊗_R A` of the induced map. -/
noncomputable def PolynomialPresentation.baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A)) :
    PolynomialPresentation
      (Algebra.TensorProduct.includeLeft :
        R' →ₐ[R] TensorProduct R R' A).toRingHom := by
  let P' := MvPolynomial (Fin p.variableCount) R'
  let q : P' →+* TensorProduct R R' A :=
    MvPolynomial.eval₂Hom (algebraMap R' (TensorProduct R R' A))
      (fun i => (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i))
  refine ⟨p.variableCount, q, ?_, ?_⟩
  · ext r
    simp [q]
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul r a =>
        obtain ⟨x, rfl⟩ := p.surjective a
        have hpoly : q.comp (MvPolynomial.map (algebraMap R R')) =
            (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom.comp
              p.toRingHom := by
          apply MvPolynomial.ringHom_ext
          · intro s
            have hp : p.toRingHom (MvPolynomial.C s) = algebraMap R A s := by
              simpa only [RingHom.comp_apply] using
                congrArg (fun h : R →+* A => h s) p.commutes
            change MvPolynomial.eval₂Hom (algebraMap R' (TensorProduct R R' A))
                (fun i => (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i))
                (MvPolynomial.map (algebraMap R R') (MvPolynomial.C s)) =
              (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A)
                (p.toRingHom (MvPolynomial.C s))
            rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, hp]
            change algebraMap R' (TensorProduct R R' A) (algebraMap R R' s) =
              (1 : R') ⊗ₜ[R] algebraMap R A s
            rw [← IsScalarTower.algebraMap_apply R R' (TensorProduct R R' A)]
            rw [Algebra.TensorProduct.algebraMap_apply']
          · intro i
            change MvPolynomial.eval₂Hom (algebraMap R' (TensorProduct R R' A))
                (fun i => (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i))
                (MvPolynomial.map (algebraMap R R') (MvPolynomial.X i)) =
              (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A)
                (p.toRingHom (MvPolynomial.X i))
            rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
            rfl
        refine ⟨MvPolynomial.C r * MvPolynomial.map (algebraMap R R') x, ?_⟩
        have hx : q (MvPolynomial.map (algebraMap R R') x) =
            (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A)
              (p.toRingHom x) :=
          congrArg (fun h : MvPolynomial (Fin p.variableCount) R →+*
            TensorProduct R R' A => h x) hpoly
        calc
          q (MvPolynomial.C r * MvPolynomial.map (algebraMap R R') x) =
              q (MvPolynomial.C r) * q (MvPolynomial.map (algebraMap R R') x) :=
            map_mul q _ _
          _ = (r ⊗ₜ[R] (1 : A)) * (1 ⊗ₜ[R] p.toRingHom x) := by
            rw [MvPolynomial.eval₂Hom_C, hx]
            rfl
          _ = r ⊗ₜ[R] p.toRingHom x := by
            rw [Algebra.TensorProduct.tmul_mul_tmul]
            simp
    | add x y hx hy =>
        rcases hx with ⟨x', rfl⟩
        rcases hy with ⟨y', rfl⟩
        exact ⟨x' + y', by simp [q]⟩

/-- The pushout `A ⊗_P P'` of a base-changed polynomial presentation is the base-changed
algebra `R' ⊗_R A`. -/
noncomputable def pushoutEquiv
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A))
    [Algebra (MvPolynomial (Fin p.variableCount) R) A]
    [Algebra (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')]
    [IsScalarTower R (MvPolynomial (Fin p.variableCount) R) A]
    [IsScalarTower R (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')]
    [IsScalarTower R R' (MvPolynomial (Fin p.variableCount) R')]
    [Algebra.IsPushout R R' (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')] :
    let P := MvPolynomial (Fin p.variableCount) R
    let P' := MvPolynomial (Fin p.variableCount) R'
    TensorProduct P A P' ≃+* TensorProduct R R' A := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  letI : Algebra P' (TensorProduct P A P') := Algebra.TensorProduct.rightAlgebra
  exact ((Algebra.TensorProduct.commRight P P' A).toRingEquiv.symm).trans
    (Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A).toRingEquiv

/-- The surjection of the base-changed presentation is the inclusion `P' → A ⊗_P P'` read
through `Dualizing.pushoutEquiv`. -/
lemma baseChange_toRingHom_eq
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A))
    [Algebra (MvPolynomial (Fin p.variableCount) R) A]
    [Algebra (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')]
    [IsScalarTower R (MvPolynomial (Fin p.variableCount) R) A]
    [IsScalarTower R (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')]
    [IsScalarTower R R' (MvPolynomial (Fin p.variableCount) R')]
    [Algebra.IsPushout R R' (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R')]
    (hp : algebraMap (MvPolynomial (Fin p.variableCount) R) A = p.toRingHom)
    (hmap : algebraMap (MvPolynomial (Fin p.variableCount) R)
      (MvPolynomial (Fin p.variableCount) R') = MvPolynomial.map (algebraMap R R')) :
    let P := MvPolynomial (Fin p.variableCount) R
    let P' := MvPolynomial (Fin p.variableCount) R'
    (PolynomialPresentation.baseChange p).toRingHom =
      (pushoutEquiv p).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          P' →ₐ[P] TensorProduct P A P').toRingHom := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P' (TensorProduct P A P') := Algebra.TensorProduct.rightAlgebra
  apply MvPolynomial.ringHom_ext
  · intro r
    let c := Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
    change MvPolynomial.eval₂Hom (algebraMap R' (TensorProduct R R' A))
        (fun i => (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i)) (MvPolynomial.C r) =
      (pushoutEquiv p)
        ((Algebra.TensorProduct.includeRight :
          P' →ₐ[P] TensorProduct P A P') (MvPolynomial.C r))
    rw [MvPolynomial.eval₂Hom_C]
    symm
    change c ((Algebra.TensorProduct.commRight P P' A).symm
        (1 ⊗ₜ[P] MvPolynomial.C r)) = algebraMap R' (TensorProduct R R' A) r
    apply c.symm.injective
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.commutes,
      Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.commRight_symm_tmul]
    congr 1
  · intro i
    change Fin p.variableCount at i
    let c := Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
    change MvPolynomial.eval₂Hom (algebraMap R' (TensorProduct R R' A))
        (fun i => (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i)) (MvPolynomial.X i) =
      (pushoutEquiv p)
        ((Algebra.TensorProduct.includeRight :
          P' →ₐ[P] TensorProduct P A P') (MvPolynomial.X i))
    rw [MvPolynomial.eval₂Hom_X']
    symm
    change c ((Algebra.TensorProduct.commRight P P' A).symm
        (1 ⊗ₜ[P] MvPolynomial.X i)) =
      (1 : R') ⊗ₜ[R] p.toRingHom (MvPolynomial.X i)
    apply c.symm.injective
    rw [AlgEquiv.symm_apply_apply, Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
    rw [Algebra.TensorProduct.commRight_symm_tmul]
    rw [show (MvPolynomial.X i : P') = algebraMap P P' (MvPolynomial.X i) by
      rw [hmap, MvPolynomial.map_X]]
    rw [show p.toRingHom (MvPolynomial.X i) =
      algebraMap P A (MvPolynomial.X i) by rw [← hp]]
    simpa [Algebra.smul_def] using
      (TensorProduct.smul_tmul (MvPolynomial.X i : P) (1 : P') (1 : A))

/-- A flat ring homomorphism stays flat after adjoining variables, the polynomial algebra
over the target being a base change of the one over the source. -/
lemma mvPolynomial_map_flat_of_flat
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (σ : Type*) (hf : (algebraMap R R').Flat) :
    (MvPolynomial.map (algebraMap R R') : MvPolynomial σ R →+* MvPolynomial σ R').Flat := by
  let : Module.Flat R R' := RingHom.flat_algebraMap_iff.mp hf
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := R')
  have e : TensorProduct R (MvPolynomial σ R) R' ≃ₗ[MvPolynomial σ R] MvPolynomial σ R' :=
    (Algebra.IsPushout.out (R := R) (S := MvPolynomial σ R) (R' := R')
      (S' := MvPolynomial σ R')).equiv
  have : Module.Flat (MvPolynomial σ R) (MvPolynomial σ R') :=
    Module.Flat.of_linearEquiv e.symm
  rw [← MvPolynomial.algebraMap_def, RingHom.flat_algebraMap_iff]
  infer_instance

/-- A flat `R`-algebra `B` is Tor independent from every `R`-algebra `A`: the vanishing of
`Torᵢ^R(A, B)` in positive degrees is the vanishing of `Torᵢ^R(B, A)` by the symmetry of Tor,
and tensoring with a flat module preserves the exactness of a projective resolution. -/
@[sga "6 VIII 1.4" "partial", sga "7 VIII 1.2" "special case"]
theorem torIndependent_of_flat_right
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Flat R B] :
    RingTheory.TorIndependence.TorIndependent R A B := by
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨e⟩ := tor_symm_canonically_iso R (k + 1)
  refine IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of R B) (ModuleCat.of R A) k) ?_
  simpa [Functor.flip] using (e.app (ModuleCat.of R A)).app (ModuleCat.of R B)

/-- Derived extension of scalars along a flat homomorphism. -/
noncomputable def flatDerivedExtension {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) := by
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  exact (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory

/-- The comparison exhibiting `Dualizing.flatDerivedExtension` as a left derived functor of
extension of scalars. -/
noncomputable def flatDerivedExtensionComparison
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    DerivedCategory.Q ⋙ flatDerivedExtension f hf ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := by
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  exact (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.hom

/-- Extension of scalars along a flat homomorphism is exact, so the functor it induces on
derived categories is its own left derived functor. -/
theorem flatDerivedExtension_isLeftDerivedFunctor
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    (flatDerivedExtension f hf).IsLeftDerivedFunctor
      (flatDerivedExtensionComparison f hf)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    extendScalars_preservesFiniteLimits_of_flat' f hf
  exact Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- The map from `A` to `R' ⊗[R] A` is flat when `R → R'` is flat. -/
lemma flat_includeRight (hf : (algebraMap R R').Flat) :
    (Algebra.TensorProduct.includeRight :
      A →ₐ[R] TensorProduct R R' A).toRingHom.Flat := by
  have hbase : (algebraMap A (TensorProduct R A R')).Flat :=
    RingHom.Flat.isStableUnderBaseChange.tensorProduct A hf
  have hcomm :
      (Algebra.TensorProduct.comm R A R').toRingEquiv.toRingHom.Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R A R').bijective
  have h := hbase.comp hcomm
  convert h using 1
  ext
  simp


/-- The hypothesis `hAct` of `Dualizing.isIso_derivedHomBaseChange_app_of_flat`, quantified over
every square: for all rings `B`, `C`, `B'` in one universe with `C` and `B'` Tor independent over
`B`, and for every pair of models of derived extension of scalars along `B → B'` and along
`C → C ⊗_B B'`, the two algebra actions `Dualizing.algebraActionLeftCanonical` and
`Dualizing.algebraActionRightCanonical` agree on the classes of K-flat complexes of `C`-modules.

This is the compatibility of the two projection formulas with the restriction/base-change
identification of [stacks 0661] discussed in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ProjectionCompatibility`, in the reduced
form of `Dualizing.projectionFormulaCompatibilityCanonical_of_kFlatAlgebraAction`.  It mentions
neither the object at which invertibility is asserted nor any finiteness hypothesis, and it is
the single hypothesis of the library's general [stacks 0BZM] beyond those of the source.  The
flat case at the exact models, which is what [stacks 0BZN] uses, does not need it. -/
def KFlatAlgebraActionEq : Prop :=
  ∀ {B C B' : Type u} [CommRing B] [CommRing C] [CommRing B'] [Algebra B C] [Algebra B B']
    (hTor : RingTheory.TorIndependence.TorIndependent B C B')
    (bc : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B'))
    (cmp : DerivedCategory.Q ⋙ bc ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ld : bc.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (bcC : DerivedCategory (ModuleCat.{u} C) ⥤
      DerivedCategory (ModuleCat.{u} (TensorProduct B C B')))
    (cmpC : DerivedCategory.Q ⋙ bcC ⟶
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap C (TensorProduct B C B'))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (ldC : bcC.IsLeftDerivedFunctor cmpC
      (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ)))
    (X : CochainComplex (ModuleCat.{u} C) ℤ), CochainComplex.KFlat.{u, u} X →
    (algebraActionLeftCanonical.{u, u, u, 0} hTor bc cmp ld bcC cmpC ldC).app
        (DerivedCategory.Q.obj X) =
      (algebraActionRightCanonical.{u, u, u, 0} hTor bc cmp ld bcC cmpC ldC).app
        (DerivedCategory.Q.obj X)

/-- **`Dualizing.KFlatAlgebraActionEq` from the tensor-comparison obligation.**  The hypothesis
`hAct` carried by the library's general [stacks 0BZM] follows from
`Dualizing.TensorComparisonCompatibility` — the identity
`μ ≫ tensorComparisonOfIso = 𝟙 ⊗ derivedBaseChangeAlgebraIso` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionTensorComparison` — at the
canonical models of every Tor-independent square of rings in one universe, by
`Dualizing.algebraActionCanonical_app_eq_of_tensorComparisonCompatibility`.

The K-flatness hypothesis on the complex of `C`-modules is not used: the obligation is checked at
a variable of `D(B)`, where a K-flat representative over `B` is available, and not at the given
object of `D(C)`. -/
theorem kFlatAlgebraActionEq_of_tensorComparisonCompatibility
    (h : ∀ {B C B' : Type u} [CommRing B] [CommRing C] [CommRing B'] [Algebra B C]
      [Algebra B B']
      (hTor : RingTheory.TorIndependence.TorIndependent B C B')
      (bc : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B'))
      (cmp : DerivedCategory.Q ⋙ bc ⟶
        (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (ld : bc.IsLeftDerivedFunctor cmp
        (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
      (bcC : DerivedCategory (ModuleCat.{u} C) ⥤
        DerivedCategory (ModuleCat.{u} (TensorProduct B C B')))
      (cmpC : DerivedCategory.Q ⋙ bcC ⟶
        (ModuleCat.extendScalars.{u, u, u}
          (algebraMap C (TensorProduct B C B'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (ldC : bcC.IsLeftDerivedFunctor cmpC
        (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ)))
      (X : DerivedCategory (ModuleCat.{u} B)),
      @TensorComparisonCompatibility.{u, u, u, 0} B C B' _ _ _ _ _ hTor bc cmp bcC cmpC
        (canonicalExtensionModel.{u, u, u} B C).functor
        (canonicalExtensionModel.{u, u, u} B C).comparison
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').functor
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').comparison
        (canonicalExtensionModel.{u, u, u} B C).isLeftDerived ldC ld
        (canonicalExtensionModelIncludeRight.{u, u, u, u} B C B').isLeftDerived X) :
    KFlatAlgebraActionEq.{u} := by
  intro B C B' _ _ _ _ _ hTor bc cmp ld bcC cmpC ldC X _
  exact @algebraActionCanonical_app_eq_of_tensorComparisonCompatibility.{u, u, u, 0} B C B'
    _ _ _ _ _ hTor bc cmp bcC cmpC ldC ld (DerivedCategory.Q.obj X)
    (h hTor bc cmp ld bcC cmpC ldC _)

end Dualizing

end
