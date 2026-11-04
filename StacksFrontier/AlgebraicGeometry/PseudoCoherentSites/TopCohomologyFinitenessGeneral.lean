module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral

/-!
# Finite type of the top cohomology of a pseudo-coherent complex, at independent universes

Let `(C, O)` be a ringed site and let `K` be an `m`-pseudo-coherent object of the derived
category of `O`-modules whose cohomology vanishes above `m`. Then `H^m(K)` is of finite type.
This holds at a ringed site `RingedSite.{u, v, w}` with modules `SheafOfModules.{w}`: locally `K`
is computed by a strictly perfect complex `P` concentrated in degrees at most `m`, whose top
cohomology is a quotient of its top term, a direct summand of a finite free module.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteType_homology_general`: the top cohomology of an
  `m`-pseudo-coherent object with vanishing higher cohomology is of finite type, at independent
  universes.

## References

* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

/-- A cochain complex with nothing one degree above `m` has its degree-`m` cohomology as a
quotient of its degree-`m` term. -/
private theorem _root_.CochainComplex.exists_epi_homology_of_isZero_X_succ {C : Type*}
    [Category C] [Abelian C] (P : CochainComplex C ℤ) (m : ℤ) (h : IsZero (P.X (m + 1))) :
    ∃ f : P.X m ⟶ P.homology m, Epi f := by
  have : IsIso (P.iCycles m) :=
    KernelFork.IsLimit.isIso_ι (KernelFork.ofι (P.iCycles m) (P.iCycles_d m (m + 1)))
      (P.cyclesIsKernel m (m + 1) (by simp)) (h.eq_of_tgt _ _)
  exact ⟨inv (P.iCycles m) ≫ P.homologyπ m, inferInstance⟩

/-- The degree-`m` cohomology of an `m`-pseudo-coherent object of the derived category of modules
over a ringed site `RingedSite.{u, v, w}`, whose cohomology vanishes above `m`, is of finite
type. -/
@[stacks 08FX "finite_type_top_cohomology, at independent universes"]
theorem isFiniteType_homology_general (X : RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hK : X.IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).obj K).IsFiniteType := by
  classical
  let A := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let R₀ := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let H := (DerivedCategory.homologyFunctor A m).obj K
  obtain ⟨E, hEK, hlocal⟩ :=
    exists_local_strictlyPerfect_approximation_boundedAbove_general X K m m le_rfl hK hvanish
  choose S hScov hS using hlocal
  let I := {V : X.C // ∃ U : X.C, ∃ f : V ⟶ U, S U f}
  let V (i : I) := i.1
  have hcover : X.J.CoversTop V := fun U =>
    X.J.superset_covering
      ((Sieve.generate_le_iff _ _).2 fun Z f hf => ⟨⟨Z, U, f, hf⟩, ⟨𝟙 Z⟩⟩) (hScov U)
  have hgen : ∀ i : I, ∃ σ : (H.over (V i)).GeneratingSections, σ.IsFiniteType := by
    intro i
    let W := i.1
    obtain ⟨U, f, hf⟩ := i.2
    obtain ⟨P, hP, hbound, α, _, hepi⟩ := hS U f hf
    have : HasSheafify (X.J.over W) AddCommGrpCat.{w} := inferInstance
    have : (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance
    let F := SheafOfModules.overFunctor R₀ W
    have : PreservesFiniteLimits F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
    have : Functor.PreservesEpimorphisms F :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms W
    have : F.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels F
    let hEhom : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology m ≅
        F.obj (E.homology m) := (E.sc m).mapHomologyIso F
    let hFac := (DerivedCategory.homologyFunctorFactors A m).app E
    let eK : (DerivedCategory.homologyFunctor A m).obj (DerivedCategory.Q.obj E) ≅ H :=
      (DerivedCategory.homologyFunctor A m).mapIso (Classical.choice hEK)
    let hTarget : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).homology m ≅
        F.obj H := hEhom ≪≫ F.mapIso hFac.symm ≪≫ F.mapIso eK
    obtain ⟨n, iP, rP, hir⟩ :=
      (isDirectSummandOfFiniteFree_iff_free _ _).mp (hP.termDirectSummand m)
    obtain ⟨fTerm, _⟩ := P.exists_epi_homology_of_isZero_X_succ m (hbound (m + 1) (by omega))
    have : IsSplitEpi rP := IsSplitEpi.mk' ⟨iP, hir⟩
    have : Epi (HomologicalComplex.homologyMap α m) := hepi
    let fFree : SheafOfModules.free (R := R₀.over W) (ULift.{w} (Fin n)) ⟶ H.over W :=
      rP ≫ fTerm ≫ HomologicalComplex.homologyMap α m ≫ hTarget.hom
    have : Epi fFree := by
      dsimp [fFree]
      infer_instance
    exact ⟨(SheafOfModules.free.generatingSections
        (R := R₀.over W) (ULift.{w} (Fin n))).ofEpi fFree,
      ⟨inferInstanceAs (Finite (ULift.{w} (Fin n)))⟩⟩
  choose σ hσ using hgen
  exact ⟨{ I := I, X := V, coversTop := hcover, generators := σ }, ⟨hσ⟩⟩

end AlgebraicGeometry.RingedSite

end
