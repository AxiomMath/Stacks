module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperGeometricFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ClosedPartFiniteSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage

/-!
# Finite stalks of the higher direct images of a proper family of curves

Let `f : X ⟶ S` be proper with all fibres of dimension at most one and `A` a finite abelian
group. Then the stalks of `Rᵠ f_* A` at the geometric points of `S` are finite. By proper base
change in the form of [Stacks, Tag 0DDF] the stalk at `s̄ : Spec Ω ⟶ S` is `Hᵠ(X_{s̄}, A)`, where
`X_{s̄} = X ×_S Spec Ω` is proper over the algebraically closed field `Ω` of dimension at most one
(its local dimensions are those of the fibre of `f` through the image point, [Stacks, Tag 02FY]),
and this cohomology group is finite by statement (5) of Situation 0A52 ([Stacks, Tag 0A57]).

## Main results

* `Stacks.EtaleCohomology.topologicalKrullDim_pullback_le_of_subsingleton`: a base change of `f`
  to a one-point scheme has dimension at most the bound on the fibres of `f`.
* `Stacks.EtaleCohomology.finite_smallEtaleStalkAb_rightDerived_constantSheaf_of_isProper`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **The base change of `f` to a one-point scheme has dimension at most the bound on the
fibres of `f`**: for `x'` in `X' = X ×_S T`, the dimension of `X'` at `x'` is that of the fibre
of `X' ⟶ T` through `x'`, which is all of `X'`, and by [Stacks, Tag 02FY] part (1) it is the
dimension at the image of `x'` of the fibre of `f`. -/
theorem topologicalKrullDim_pullback_le_of_subsingleton {X S T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (y : T ⟶ S) [Subsingleton T] {n : WithBot ℕ∞}
    (h : ∀ s, topologicalKrullDim (f.fiber s) ≤ n) :
    topologicalKrullDim (pullback (C := Scheme.{u}) f y : Type u) ≤ n := by
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x' => ?_
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  let g := pullback.snd f y
  have hsurj : Function.Surjective (g.fiberι (g x')) := fun z => by
    rw [← Set.mem_range, Scheme.Hom.range_fiberι]
    exact Subsingleton.elim (g z) (g x')
  let φ := (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(g.fiberι (g x')).isEmbedding, hsurj⟩).homeomorph
  calc topologicalKrullDimAt (pullback (C := Scheme.{u}) f y : Type u) x'
      ≤ topologicalKrullDimAt (g.fiber (g x')) (φ.symm x') :=
        topologicalKrullDimAt_le_of_isEmbedding φ.symm.isEmbedding x'
    _ = topologicalKrullDimAt (f.fiber (f (pullback.fst f y x')))
          (f.asFiber (pullback.fst f y x')) := by
        rw [φ.symm_apply_eq.2 (g.fiberι_asFiber x').symm]
        exact topologicalKrullDimAt_fiber_eq_of_isPullback (IsPullback.of_hasPullback f y) x'
    _ ≤ topologicalKrullDim (f.fiber (f (pullback.fst f y x'))) :=
        topologicalKrullDimAt_le_topologicalKrullDim _
    _ ≤ n := h _

/-- **The stalks of `Rᵠ f_* A` are finite** for `f : X ⟶ S` proper with fibres of dimension at most
one and `A` a finite abelian group: by [Stacks, Tag 0DDF] the stalk at a geometric point `s̄` is
`Hᵠ(X_{s̄}, A)`, which is finite by [Stacks, Tag 0A57], `X_{s̄}` being a proper scheme of dimension
at most one over an algebraically closed field and `A` a constructible sheaf on it. -/
theorem finite_smallEtaleStalkAb_rightDerived_constantSheaf_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (hdim : ∀ s, topologicalKrullDim (f.fiber s) ≤ 1)
    (s : GeometricPoint S) (A : AddCommGrpCat.{u + 1}) [Finite A] (q : ℕ) :
    Finite ((smallEtaleStalkAb s.hom).obj (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A))) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  have hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F :=
    Stacks.Torsion.torsionSheafProperty_constantSheaf X.smallEtaleTopology A
  let X' := pullback f s.hom
  let := hasExt_sheaf_smallEtale_succ X'
  let g' := pullback.fst f s.hom
  let F' := (etaleAbelianInverseImage.{u, 0} g').obj F
  let S0 : TorsionSheafSituation.{u, 0} :=
    { k := s.residueField
      X := X'
      structureMorphism := pullback.snd f s.hom
      dimension_le_one := topologicalKrullDim_pullback_le_of_subsingleton f s.hom hdim
      F := F'
      isTorsion := torsionSheafProperty_etaleAbelianInverseImage.{u, 0} g' F hF }
  let B' := BigEtaleSite.containing X'
  let hX' := BigEtaleSite.contains_containing X'
  have hc : IsConstructibleEtaleAbelianSheaf.{u, 0} B' X' hX' F' :=
    isConstructibleFiniteSheaf_congr B' (B'.obj X' hX')
      ((SmallEtale.sheafEquiv B' X' hX' AddCommGrpCat.{u + 1}).inverse.mapIso
        ((etaleAbelianInverseImageConstantIso.{u, 0} g').app A).symm)
      (isConstructibleEtaleAbelianSheaf_constantSheaf.{u, 0} X' A)
  have : Finite (AddCommGrpCat.of (Sheaf.H.{u + 1} F' q)) :=
    S0.finiteCohomologyOfIsProper B' hX' (inferInstanceAs (IsProper (pullback.snd f s.hom))) hc q
  let P := (((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj F).obj
  let e0 : ((Scheme.pointSmallEtale s.hom).ulift.{u + 1}).presheafFiber.obj P ≅
      (Scheme.pointSmallEtale s.hom).presheafFiber.obj P :=
    ((Scheme.pointSmallEtale s.hom).uliftPresheafFiberIso (A := AddCommGrpCat.{u + 1})).app P
  exact Finite.of_equiv _ (e0.symm ≪≫ etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper
    f s.hom F hF q).symm.addCommGroupIsoToAddEquiv.toEquiv

end Stacks.EtaleCohomology

end
