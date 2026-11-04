module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComparisonFunctorial
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AcyclicCoveringComputesDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CandidateKInjectiveResolution

/-!
# The alternating Čech comparison at one stage of a candidate K-injective resolution

Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be a *finite* open covering of `X`, let
`F^•` be an arbitrary complex of `O_X`-modules and let `C` be a candidate K-injective
resolution of `F^•` in the sense of Tag 071A: a tower of bounded below complexes of injectives
`I_n` together with quasi-isomorphisms `f_n : τ_{≥ -n} F^• ⟶ I_n`. Assume, as in condition (3)
of Tag 08C2, that there is a set `B` of opens containing every finite intersection of members
of the covering on which the terms of `F^•` and the cokernels of its differentials are
acyclic. Then for every `n` the induced map of *total alternating* Čech complexes

`Tot(Č_alt^•(U, τ_{≥ -n} F^•)) ⟶ Tot(Č_alt^•(U, I_n))`

is a quasi-isomorphism.

## Main results

* `Stacks.Cech.isZero_rightDerived_truncGE_X`: under conditions (3)(a) and (3)(b) of Tag 08C2,
  every term of every canonical truncation of `F^•` is acyclic for sections over every member
  of `B`.
* `Stacks.Cech.quasiIso_cechTotalMap_candidateStage`: the same conclusion for the total
  ordinary Čech complexes.
* `Stacks.Cech.quasiIso_alternatingCechTotalMap_candidateStage`: the conclusion.

## References

* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 071A](https://stacks.math.columbia.edu/tag/071A)
* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

noncomputable section

attribute [local instance] additive_sheafOfModulesEvaluation

/-! ### Acyclicity of the terms of a canonical truncation -/

/-- The opcycles of a cochain complex in degree `a` as the cokernel of the differential
arriving in degree `a`. -/
private def opcyclesIsoCokernelPred {A : Type*} [Category A] [Abelian A]
    (K : CochainComplex A ℤ) (a : ℤ) :
    K.opcycles a ≅ cokernel (K.d (a - 1) a) :=
  IsColimit.coconePointUniqueUpToIso
    (K.opcyclesIsCokernel (i := a - 1) (j := a) (CochainComplex.prev ℤ a))
    (colimit.isColimit (parallelPair (K.d (a - 1) a) 0))

variable (X : TopCat.{u})

/-- **Conditions (3)(a) and (3)(b) of Tag 08C2 make every term of every canonical truncation
acyclic.** If the terms of `F^•` and the cokernels of its differentials have vanishing higher
derived sections over an open `W`, then so does every term of every canonical truncation
`τ_{≥ a} F^•`. -/
theorem isZero_rightDerived_truncGE_X
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) (B : Set (Opens X))
    (h_terms : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.X q)))
    (h_cokernels : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj
        (cokernel (F.d (q - 1) q))))
    (W : Opens X) (hW : W ∈ B) (a q : ℤ) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj
      ((F.truncGE a).X q)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = m + 1 := ⟨p - 1, by omega⟩
  by_cases haq : a < q
  · exact (h_terms W hW q _ hp).of_iso
      (Functor.mapIso _ (CochainComplex.truncGEXIso F a q haq))
  · by_cases hqa : q < a
    · have : Injective ((F.truncGE a).X q) :=
        (CochainComplex.isZero_of_isStrictlyGE (F.truncGE a) a q hqa).injective
      exact Functor.isZero_rightDerived_obj_injective_succ _ m _
    · obtain rfl : q = a := le_antisymm (not_lt.1 haq) (not_lt.1 hqa)
      exact (h_cokernels W hW _ _ hp).of_iso
        (Functor.mapIso _
          (CochainComplex.truncGEXIsoOpcycles F _ ≪≫ opcyclesIsoCokernelPred F _))

/-! ### The comparison at one stage of the resolution -/

/-- **The ordinary Čech form of the conclusion.** With conditions (3)(a) and (3)(b) of
Tag 08C2 in force on a set of opens containing the finite intersections of the covering, the
map of total Čech complexes induced by the `n`-th stage `f_n : τ_{≥ -n} F^• ⟶ I_n` of a
candidate K-injective resolution is a quasi-isomorphism. -/
theorem quasiIso_cechTotalMap_candidateStage
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I : Type u} (U : I → Opens X)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F)
    (B : Set (Opens X))
    (h_inter : ∀ (p : ℕ) (s : Fin (p + 1) → I), (⨅ k, U (s k)) ∈ B)
    (h_terms : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.X q)))
    (h_cokernels : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj
        (cokernel (F.d (q - 1) q))))
    (n : ℕ) :
    QuasiIso ((cechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n))) := by
  have hGE := C.strictlyGE_I n
  have hqf : QuasiIso (C.f n) := C.quasiIso_f n
  exact quasiIso_cechTotalComplexFunctor_map X U R (C.f n) ⟨-(n : ℤ), inferInstance⟩
    ⟨-(n : ℤ), hGE⟩ (-(n : ℤ))
    (fun q hq ↦ CochainComplex.isZero_of_isStrictlyGE (F.truncGE (-(n : ℤ))) (-(n : ℤ)) q hq)
    (fun q hq ↦ CochainComplex.isZero_of_isStrictlyGE (C.I n) (-(n : ℤ)) q hq) (C.injective_I n)
    (fun m s q i hi ↦
      isZero_rightDerived_truncGE_X X R F B h_terms h_cokernels _ (h_inter m s) _ q i hi)

/-- **The alternating Čech comparison at one stage of a candidate K-injective resolution.**
With conditions (3)(a) and (3)(b) of Tag 08C2 in force on a set of opens containing the finite
intersections of a finite covering, the map of total *alternating* Čech complexes induced by
the `n`-th stage `f_n : τ_{≥ -n} F^• ⟶ I_n` of a candidate K-injective resolution is a
quasi-isomorphism. -/
theorem quasiIso_alternatingCechTotalMap_candidateStage
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I : Type u} [Finite I] (U : I → Opens X) (_hU : (⊤ : Opens X) = iSup U)
    (F : CochainComplex (SheafOfModules.{u} R) ℤ)
    (C : Stacks.KInjective.CandidateKInjectiveResolution R F)
    (B : Set (Opens X))
    (h_inter : ∀ (p : ℕ) (s : Fin (p + 1) → I), (⨅ k, U (s k)) ∈ B)
    (h_terms : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj (F.X q)))
    (h_cokernels : ∀ W ∈ B, ∀ (q : ℤ) (p : ℕ), 0 < p →
      IsZero (((SheafOfModules.evaluation R (op W)).rightDerived p).obj
        (cokernel (F.d (q - 1) q))))
    (n : ℕ) :
    QuasiIso ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n))) := by
  classical
  have _ := Fintype.ofFinite I
  let _ : LinearOrder I :=
    LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hGE := C.strictlyGE_I n
  have hι (M : CochainComplex (SheafOfModules.{u} R) ℤ) (hM : M.IsStrictlyGE (-(n : ℤ))) :
      QuasiIso ((alternatingCechTotalInclusion U).app
        ((underlyingPresheafComplexFunctor X R).obj M)) :=
    quasiIso_alternatingCechTotalInclusion_app U _ (-(n : ℤ)) fun q hq ↦
      Functor.map_isZero (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj)
        (CochainComplex.isZero_of_isStrictlyGE M (-(n : ℤ)) q hq)
  have hιK := hι (F.truncGE (-(n : ℤ))) inferInstance
  have hιL := hι (C.I n) hGE
  have hcech : QuasiIso ((cechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n))) :=
    quasiIso_cechTotalMap_candidateStage X R U F C B h_inter h_terms h_cokernels n
  have hcomp : QuasiIso ((alternatingCechTotalComplexFunctor U).map
      ((underlyingPresheafComplexFunctor X R).map (C.f n)) ≫
      (alternatingCechTotalInclusion U).app
        ((underlyingPresheafComplexFunctor X R).obj (C.I n))) := by
    rw [(alternatingCechTotalInclusion U).naturality
      ((underlyingPresheafComplexFunctor X R).map (C.f n))]
    infer_instance
  exact quasiIso_of_comp_right (hφ := hιL) (hφφ' := hcomp) _ _

end

end Stacks.Cech

end
