module

public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermDoubleQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermFlatBaseChange
public import StacksFrontier.RingTheory.Rig.IdealIndependence
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CompletionLimit
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.DerivedCompletion

/-!
# The completed naive cotangent complex is the derived base change

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `A → B` be of finite type and let
`α : A[x₁, …, xₙ] → B` be a presentation.  The second clause of Stacks 0GAF reads

`NL^∧_{B^/A} = NL_{B/A} ⊗^L_B B^`  in  `D(B^)`.

Three facts combine to it.  The naive cotangent complex of the canonical presentation of `B`
over `A` is homotopy equivalent to `NL(α)` (Stacks 00S1), so after base change along `B → B^`
the two become quasi-isomorphic — `B → B^` is flat, so flat base change preserves
quasi-isomorphy.  The base change of `NL(α)` is `NL^∧_{B^/A}` on the nose, by the first clause
of Stacks 0GAF.  And derived base change along the flat map `B → B^` is ordinary base change,
which is `Rig.flatDerivedTensorIso`.

## Main definitions

* `Rig.naiveCotangentTwoTerm` and `Rig.naiveCotangentCochain` — `NL_{B/A}`, the naive cotangent
  complex of the canonical presentation `A[B] → B`, as a two-term complex and as a cochain
  complex of `B`-modules with the conormal module in degree `-1`.
* `Rig.nlPresentationComparison` — the comparison `NL_{B/A} → NL(α)` of Stacks 00S1.
* `Rig.extendScalarsNaiveCotangentIso` — extension of scalars along `B → B^` applied to
  `NL_{B/A}` is the base change `NL_{B/A} ⊗_B B^`.
* `Rig.presentationBaseChangeCochainIso` — `NL(α) ⊗_B B^ = NL^∧_{B^/A}` as cochain complexes.

## Main results

* `Rig.quasiIso_nlPresentationComparisonBaseChange` — `NL_{B/A} ⊗_B B^ → NL(α) ⊗_B B^` is a
  quasi-isomorphism.
* `Rig.completedNaiveCotangentDerivedIso` — **Stacks 0GAF, second clause**:
  `NL^∧_{B^/A} = NL_{B/A} ⊗^L_B B^` in `D(B^)`, for any normalized derived base change along
  `B → B^`.
* `Rig.completedNaiveCotangentDerivedTensorIso` — the same for the canonical derived tensor
  product with the unit complex `B^`.

## Implementation notes

`NL_{B/A}` is rendered as the cochain complex concentrated in degrees `-1` and `0` attached to
the differential of the canonical presentation `A[B] → B`; that is the same convention under
which `Rig.CompletedNaiveCotangentComplex.cochainComplex` renders `NL^∧_{B^/A}`, and the one the
derived category of `B` is taken over here.

## References

* [Stacks Project, Lemma 88.3.2 (Tag 0GAF)](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Lemma 10.97.2 (Tag 00MB)](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Lemma 10.134.2 (Tag 00S1)](https://stacks.math.columbia.edu/tag/00S1)
-/

@[expose] public noncomputable section

open CategoryTheory NaiveCotangent

open scoped TensorProduct

universe u v

namespace Rig

attribute [local instance] HasDerivedCategory.standard

/-- The two degrees in which a two-term complex sits are related in the cochain shape. -/
public theorem upRelNegOneZero : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 := rfl

/-- `NL_{B/A}`, the naive cotangent complex of `B` over `A` taken at the canonical presentation
`A[B] → B`, as a two-term complex of `B`-modules. -/
public abbrev naiveCotangentTwoTerm (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    [Algebra A B] : NaiveCotangent.TwoTerm B :=
  NaiveCotangent.nlRestrict B (Algebra.Generators.self A B)

/-- `NL_{B/A}` as a cochain complex of `B`-modules, with the conormal module in degree `-1` and
the module of differentials in degree `0`. -/
public abbrev naiveCotangentCochain (A : Type u) [CommRing A] (B : Type v) [CommRing B]
    [Algebra A B] : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom (naiveCotangentTwoTerm A B).d) upRelNegOneZero

section Derived

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B] {n : ℕ}
  (G : Algebra.Generators A B (Fin n))

include G in
/-- **Stacks 00S1.** The comparison `NL_{B/A} → NL(α)` of naive cotangent complexes attached to
the canonical presentation `A[B] → B` and to `α : A[x₁, …, xₙ] → B`. -/
public def nlPresentationComparison :
    ChainMap (naiveCotangentTwoTerm A B) (nlRestrict B G) :=
  nlMap (Algebra.Generators.self A B) G ((Algebra.Generators.self A B).defaultHom G)

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
include G in
/-- **Stacks 00S1.** The comparison `NL_{B/A} → NL(α)` is a quasi-isomorphism, being a homotopy
equivalence. -/
public theorem quasiIso_nlPresentationComparison :
    IsQuasiIso (nlPresentationComparison (A := A) G) :=
  (nlMap_isHomotopyEquiv_and_isQuasiIso Function.bijective_id Function.bijective_id
    (Algebra.Generators.self A B) G ((Algebra.Generators.self A B).defaultHom G)).2

include G in
/-- The base change `NL_{B/A} ⊗_B B^ → NL(α) ⊗_B B^` of the comparison of Stacks 00S1. -/
public def nlPresentationComparisonBaseChange :
    ChainMap ((naiveCotangentTwoTerm A B).baseChange (adicCompletionObj I (B := B)).carrier)
      ((nlRestrict B G).baseChange (adicCompletionObj I (B := B)).carrier) :=
  (nlPresentationComparison (A := A) G).baseChange _

include G in
/-- **The base change of the comparison of Stacks 00S1 along `B → B^` is a
quasi-isomorphism**: `B → B^` is flat, because `B` is Noetherian, and flat base change
preserves quasi-isomorphy. -/
public theorem quasiIso_nlPresentationComparisonBaseChange :
    IsQuasiIso (nlPresentationComparisonBaseChange I G) := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Module.Flat B (adicCompletionObj I (B := B)).carrier :=
    AdicCompletion.flat_of_isNoetherian (I.map (algebraMap A B))
  exact (quasiIso_nlPresentationComparison (A := A) G).baseChange _

include G in
/-- The quasi-isomorphism of cochain complexes `NL_{B/A} ⊗_B B^ → NL(α) ⊗_B B^`. -/
public def nlPresentationComparisonCochain :
    HomologicalComplex.double
        (ModuleCat.ofHom
          ((naiveCotangentTwoTerm A B).baseChange
            (adicCompletionObj I (B := B)).carrier).d) upRelNegOneZero ⟶
      HomologicalComplex.double
        (ModuleCat.ofHom
          ((nlRestrict B G).baseChange (adicCompletionObj I (B := B)).carrier).d)
        upRelNegOneZero :=
  Stacks.TwoTermDoubleQuasiIso.mapDouble (nlPresentationComparisonBaseChange I G) upRelNegOneZero

include G in
/-- The comparison `nlPresentationComparisonCochain I G` of cochain complexes is a
quasi-isomorphism. -/
public instance quasiIso_nlPresentationComparisonCochain :
    QuasiIso (nlPresentationComparisonCochain I G) :=
  Stacks.TwoTermDoubleQuasiIso.quasiIso_mapDouble upRelNegOneZero
    (quasiIso_nlPresentationComparisonBaseChange I G)

/-- **Extension of scalars along `B → B^` applied to `NL_{B/A}` is the base change
`NL_{B/A} ⊗_B B^`**: extension of scalars is applied termwise to a complex concentrated in two
degrees, and in each of those degrees it is the base change of the term. -/
public def extendScalarsNaiveCotangentIso :
    (CochainComplex.extendScalarsLarge.{u, v, v}
          (algebraMap B (adicCompletionObj I (B := B)).carrier)).obj
        (naiveCotangentCochain A B) ≅
      HomologicalComplex.double
        (ModuleCat.ofHom
          ((naiveCotangentTwoTerm A B).baseChange
            (adicCompletionObj I (B := B)).carrier).d) upRelNegOneZero :=
  (HomologicalComplex.doubleMapFunctorIso
    (ModuleCat.extendScalars.{v, v, max u v}
      (algebraMap B (adicCompletionObj I (B := B)).carrier))
    (ModuleCat.ofHom (naiveCotangentTwoTerm A B).d) upRelNegOneZero (by decide)).symm

include G in
/-- **Stacks 0GAF, first clause, as an isomorphism of cochain complexes.** `NL(α) ⊗_B B^` is
`NL^∧_{B^/A}`: in degree `-1` the identification is the comparison of conormal modules
`B^ ⊗_B (J / J²) = J^ / (J^)²`, and in degree `0` both terms are free on `dx₁, …, dxₙ`. -/
public def presentationBaseChangeCochainIso :
    HomologicalComplex.double
        (ModuleCat.ofHom
          ((nlRestrict B G).baseChange (adicCompletionObj I (B := B)).carrier).d)
        upRelNegOneZero ≅
      (completedComplex I G).cochainComplex :=
  doubleIsoDouble _ _ upRelNegOneZero (by decide)
    (((LinearEquiv.ofBijective (completionComparison I G).f₁
      (bijective_completionComparison_f₁ I G)).trans ULift.moduleEquiv.symm).toModuleIso)
    ((((LinearEquiv.baseChange B (adicCompletionObj I (B := B)).carrier
        (Algebra.Extension.CotangentSpace G.toExtension) (Fin n → B)
        G.cotangentSpaceBasis.equivFun).trans
      (LinearEquiv.ofBijective (completionComparison I G).f₀
        (bijective_completionComparison_f₀ I G))).trans ULift.moduleEquiv.symm).toModuleIso)
    (by
      have hbc : ∀ w, LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
            (presentationDifferential G) w =
          LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
            G.cotangentSpaceBasis.equivFun.toLinearMap
            (LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
              ((nlRestrict B G).d) w) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul s x => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
      have hcomm := LinearMap.congr_fun (completionComparison I G).comm z
      simp only [LinearMap.coe_comp] at hcomm
      change ULift.up ((completedComplex I G).differential ((completionComparison I G).f₁ z)) =
        ULift.up ((completionComparison I G).f₀
          (LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
            G.cotangentSpaceBasis.equivFun.toLinearMap
            (LinearMap.baseChange (adicCompletionObj I (B := B)).carrier
              ((nlRestrict B G).d) z)))
      rw [← hbc z]
      exact congrArg ULift.up hcomm)

include G in
/-- **Stacks 0GAF, second clause.** `NL^∧_{B^/A} = NL_{B/A} ⊗^L_B B^` in `D(B^)`, for any
derived base change along `B → B^` normalized by the unit complex.  The chain of
identifications is: derived base change along the flat map `B → B^` is ordinary extension of
scalars; extension of scalars of `NL_{B/A}` is the base change `NL_{B/A} ⊗_B B^`; that is
quasi-isomorphic to `NL(α) ⊗_B B^`, since `NL_{B/A} → NL(α)` is a homotopy equivalence and
`B → B^` is flat; and `NL(α) ⊗_B B^` is `NL^∧_{B^/A}` by the first clause. -/
public def completedNaiveCotangentDerivedIso
    {N : CochainComplex (ModuleCat.{max u v} (adicCompletionObj I (B := B)).carrier) ℤ}
    (T : CochainComplex.DerivedTensor.DerivedTensorChangeOfRings
      (algebraMap B (adicCompletionObj I (B := B)).carrier) N)
    (hN : N.tensorRightLarge ≅
      𝟭 (CochainComplex (ModuleCat.{max u v} (adicCompletionObj I (B := B)).carrier) ℤ)) :
    T.F.obj (DerivedCategory.Q.obj (naiveCotangentCochain A B)) ≅
      DerivedCategory.Q.obj (completedComplex I G).cochainComplex := by
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hflat : (algebraMap B (adicCompletionObj I (B := B)).carrier).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (AdicCompletion.flat_of_isNoetherian (I.map (algebraMap A B)))
  haveI : IsIso (DerivedCategory.Q.map (nlPresentationComparisonCochain I G)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := nlPresentationComparisonCochain I G)).mpr
      (quasiIso_nlPresentationComparisonCochain I G)
  exact flatDerivedTensorIso _ hflat T hN (naiveCotangentCochain A B) ≪≫
    DerivedCategory.Q.mapIso (extendScalarsNaiveCotangentIso I) ≪≫
    asIso (DerivedCategory.Q.map (nlPresentationComparisonCochain I G)) ≪≫
    DerivedCategory.Q.mapIso (presentationBaseChangeCochainIso I G)

include G in
/-- **Stacks 0GAF, second clause.** `NL^∧_{B^/A} = NL_{B/A} ⊗^L_B B^` in `D(B^)`, for the
canonical derived tensor product along `B → B^` with the unit complex `B^` in degree `0`. -/
@[stacks 0GAF "NL^∧_{B^/A} = NL_{B/A} ⊗^L_B B^ in D(B^)"]
public def completedNaiveCotangentDerivedTensorIso :
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings
        (algebraMap B (adicCompletionObj I (B := B)).carrier)
        ((CochainComplex.singleFunctor
          (ModuleCat.{max u v} (adicCompletionObj I (B := B)).carrier) 0).obj
          (ModuleCat.of (adicCompletionObj I (B := B)).carrier
            (ULift.{u} (adicCompletionObj I (B := B)).carrier)))).F.obj
        (DerivedCategory.Q.obj (naiveCotangentCochain A B)) ≅
      DerivedCategory.Q.obj (completedComplex I G).cochainComplex :=
  completedNaiveCotangentDerivedIso I G _
    (tensorRightLargeUnitIso (adicCompletionObj I (B := B)).carrier)

end Derived

end Rig

end
