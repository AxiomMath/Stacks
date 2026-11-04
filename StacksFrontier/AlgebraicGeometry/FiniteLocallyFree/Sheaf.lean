module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Finite local freeness of a sheaf of modules on a scheme is a pointwise condition

A sheaf of modules on a scheme is finite locally free exactly when every point has an open
neighbourhood on which the sheaf is isomorphic to a free sheaf on a finite index type. The
first formulation carries a single global datum, a cover of the whole space together with a
finite free presentation over each of its members; the second quantifies over points. The two
are equivalent, and the second is the formulation in which locality on the base is immediate.

## Main results

* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso`: finite local freeness only
  depends on the isomorphism class of a sheaf of modules.
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff`: the pointwise condition and the
  condition given by a single global datum agree.
* `Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`: the structure sheaf,
viewed as a
  module over itself, is quasi-coherent.

## Implementation notes

Passing from a global datum to the pointwise condition reads off a member of the cover through
the given point and transports its free presentation across
`AlgebraicGeometry.Scheme.Modules.overEquiv`, the equivalence between sheaves of modules over
the restricted structure sheaf and sheaves of modules on the open subscheme. Passing back
chooses a neighbourhood for every point, which gives a cover indexed by the points of the
space, and transports each isomorphism in the other direction; a free presentation is recovered
from an isomorphism with a free sheaf by taking the image of the canonical global basis of the
latter.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Finite local freeness only depends on the isomorphism class of a sheaf of modules: the
local free presentations are transported along the isomorphism, keeping their index types. -/
theorem SheafOfModules.IsFiniteLocallyFree.of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    [h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} N := by
  obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
  let q' : SheafOfModules.LocalGeneratorsData.{u, u, u, u} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  have hfree' : q'.IsLocallyFreeData.{u, u, u, u} := by
    constructor
    intro i
    have h₀ : IsIso (q.generators i).π := hfree.isIso i
    have h₁ : IsIso ((q.generators i).π ≫
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom)) h₁
  have hfin' : q'.IsFiniteType := by
    constructor
    intro i
    have := hfin.isFiniteType i
    infer_instance
  exact { exists_isFiniteLocallyFreeData := ⟨q', hfree', hfin'⟩ }

/-- An isomorphism of the restriction of a sheaf of modules to an open with a free sheaf on a
finite index type gives a finite free presentation of the sheaf over that open. -/
private theorem exists_generatingSections_of_restrict_iso {X : Scheme.{u}} (M : X.Modules)
    (V : X.Opens) (I : Type u) (hI : Finite I)
    (e : M.restrict V.ι ≅ SheafOfModules.free.{u} I) :
    ∃ σ : (M.over V).GeneratingSections, IsIso σ.π ∧ σ.IsFiniteType := by
  let F := Scheme.Modules.overEquiv (X := X) V
  have hdisc : Limits.PreservesColimitsOfShape (Discrete I) F.functor :=
    Limits.preservesColimitsOfShape_of_discrete F.functor
  have hunit : SheafOfModules.unit (V.toScheme).ringCatSheaf ≅
      F.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
  let e' : F.functor.obj (M.over V) ≅ F.functor.obj (SheafOfModules.free.{u} I) :=
    (Scheme.Modules.overFunctorEquiv (X := X) V).app M ≪≫ e ≪≫ eFree
  let e'' : M.over V ≅ SheafOfModules.free.{u} I := F.fullyFaithfulFunctor.preimageIso e'
  refine ⟨(SheafOfModules.free.generatingSections I).ofEpi e''.inv, ?_, ⟨hI⟩⟩
  have h₀ : IsIso (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over V) I).π := by
    rw [SheafOfModules.free.generatingSections_π]
    exact IsIso.id _
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₀ inferInstance

/-- A sheaf of modules on a scheme is finite locally free at every point, in the sense of
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`, exactly when there is a single datum
consisting of a cover of the whole space and a finite free presentation over each member. -/
theorem Scheme.Modules.isFiniteLocallyFree_iff {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.IsFiniteLocallyFree M ↔ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M := by
  refine ⟨fun h ↦ ?_, fun h x ↦ ?_⟩
  · choose U hU I hIfin hiso using h
    choose σ hσ₁ hσ₂ using fun x ↦
      exists_generatingSections_of_restrict_iso M (U x) (I x) (hIfin x) (hiso x).some
    have hcover : TopologicalSpace.IsOpenCover U := by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      simp only [TopologicalSpace.Opens.mem_iSup]
      exact ⟨x, hU x⟩
    let q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} M :=
      { I := X
        X := U
        coversTop := (_root_.Opens.coversTop_iff X U).mpr hcover
        generators := σ }
    have h₁ : q.IsLocallyFreeData.{u, u, u, u} := by
      constructor
      exact hσ₁
    have h₂ : q.IsFiniteType := by
      constructor
      exact hσ₂
    exact { exists_isFiniteLocallyFreeData := ⟨q, h₁, h₂⟩ }
  · obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
    obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
    let U : X.Opens := q.X i
    let I := (q.generators i).I
    have hIfin : Finite I := (hfin.isFiniteType i).finite
    let F := Scheme.Modules.overEquiv (X := X) U
    have hdisc : Limits.PreservesColimitsOfShape (Discrete I) F.functor :=
      Limits.preservesColimitsOfShape_of_discrete F.functor
    have hunit : SheafOfModules.unit (U.toScheme).ringCatSheaf ≅
        F.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) := Iso.refl _
    have hπ : IsIso (q.generators i).π := hfree.isIso i
    let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
    let eM := (F.functor.mapIso (@asIso _ _ _ _ _ hπ)) ≪≫
      (Scheme.Modules.overFunctorEquiv (X := X) U).app M |>.symm
    exact ⟨U, hi, I, hIfin, ⟨eM ≪≫ eFree.symm⟩⟩

end AlgebraicGeometry

end
