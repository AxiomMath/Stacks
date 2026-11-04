module

public import StacksFrontier.Homology.Tor.ExtendScalarsSingleTor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback

/-!
# Pullback of a module in degree zero computes its derived pullback, under Tor vanishing

Let `f : X ⟶ Y` be a morphism of ringed spaces and `ℳ` a sheaf of `𝒪_Y`-modules such that at
every point `x` of `X` the positive Tor modules `Tor_n^{𝒪_{Y,f(x)}}(𝒪_{X,x}, ℳ_{f(x)})` vanish.
Then the degreewise pullback along `f` of *any* quasi-isomorphism from a K-flat complex to
`ℳ[0]` is again a quasi-isomorphism.

## Main definitions

All names below are in the namespace `Stacks.Cohomology.PullbackSingleTor`.

* `StalkTorVanishing`: the vanishing of the positive Tor modules of the stalks.

## Main results

* `quasiIso_modulePullback_map_of_stalkTorVanishing`: the statement above.
* `isIso_derivedPullbackComparison_app_single_of_stalkTorVanishing`: the consequence for the
  derived pullback, at an arbitrary model of the two derived categories: the canonical comparison
  `Lf^*(Qℳ[0]) ⟶ Q(f^*ℳ[0])` of [Stacks, Tag 06YJ] is invertible.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.SheafOfModules

universe u w₁ w₂

namespace Stacks.Cohomology.PullbackSingleTor

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Tor vanishing at the stalks.** At every point `x` of `X`, the positive Tor modules of the
stalk `𝒪_{X,x}` and the stalk `ℳ_{f(x)}` over the stalk `𝒪_{Y,f(x)}` vanish. The first argument
of `CategoryTheory.Tor` is `𝒪_{X,x}` read as an `𝒪_{Y,f(x)}`-module along the germ map, and the
second is the stalk of `ℳ`. -/
def StalkTorVanishing (ℳ : SheafOfModules.{u} (structureSheafRing Y)) : Prop :=
  ∀ (x : X.carrier) (n : ℕ), 0 < n →
    letI := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
    letI := Stacks.RingedSpace.structureStalkCommRing X x
    IsZero (((Tor (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj (f.hom.base x))) n).obj
      (CochainComplex.DerivedExtensionScalars.baseModule
        (Stacks.RingedSpace.stalkRingMap f x).hom)).obj
      ((stalkFunctor (structureSheafRing Y) (f.hom.base x)).obj ℳ))

/-- **The degreewise pullback of a K-flat resolution of `ℳ[0]` is a quasi-isomorphism, under Tor
vanishing at the stalks.** -/
theorem quasiIso_modulePullback_map_of_stalkTorVanishing
    {ℳ : SheafOfModules.{u} (structureSheafRing Y)} (hTor : StalkTorVanishing f ℳ)
    {P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y P)
    (π : P ⟶ (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) 0).obj ℳ) [QuasiIso π] :
    QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map π) := by
  refine AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso _ _ fun x => ?_
  let := Stacks.RingedSpace.structureStalkCommRing Y (f.hom.base x)
  let := Stacks.RingedSpace.structureStalkCommRing X x
  set φ := (Stacks.RingedSpace.stalkRingMap f x).hom
  set Sf := (stalkFunctor (structureSheafRing Y) (f.hom.base x)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let e := (HomologicalComplex.singleMapHomologicalComplex
    (stalkFunctor (structureSheafRing Y) (f.hom.base x)) (ComplexShape.up ℤ) 0).app ℳ
  have : QuasiIso (Sf.map π) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have : QuasiIso e.hom := quasiIso_of_isIso e.hom
  have hkf : CochainComplex.KFlat.{u, u} (Sf.obj P) :=
    (Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise Y.sheaf P).1 hP (f.hom.base x)
  have key : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map (Sf.map π ≫ e.hom)) :=
    CochainComplex.DerivedExtensionScalars.quasiIso_extendScalars_map_single_of_isZero_tor
      φ _ (fun n hn => hTor x n hn) hkf (Sf.map π ≫ e.hom)
  have key' : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map (Sf.map π)) := by
    rw [Functor.map_comp] at key
    have : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map e.hom) :=
      quasiIso_of_isIso _
    exact (quasiIso_iff_comp_right _ _).1 key
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    ((Stacks.RingedSpace.stalkModulePullbackComplexIso f x (ComplexShape.up ℤ)).app P)
    ((Stacks.RingedSpace.stalkModulePullbackComplexIso f x (ComplexShape.up ℤ)).app _)
    ((Stacks.RingedSpace.stalkModulePullbackComplexIso f x
      (ComplexShape.up ℤ)).hom.naturality π).symm)).2 key'

/-- A quasi-isomorphism of complexes becomes invertible in the derived category after passing
to the homotopy category. -/
private theorem isIso_Qh_map_quotient_map_of_quasiIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (p : K ⟶ L) [QuasiIso p] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map p)) :=
  Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff p).2
      ((HomologicalComplex.mem_quasiIso_iff p).2 ‹_›))

/-- **The canonical comparison `Lf^*(QM) ⟶ Q(f^*M)` is invertible at a module placed in degree
zero, under Tor vanishing at the stalks.** -/
theorem isIso_derivedPullbackComparison_app_single_of_stalkTorVanishing
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]
    {ℳ : SheafOfModules.{u} (structureSheafRing Y)} (hTor : StalkTorVanishing f ℳ) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ) 0).obj ℳ))) := by
  obtain ⟨P, p, hP, -, hp, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
    ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) 0).obj ℳ)
  set s := (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
    (ComplexShape.up ℤ)).map p
  have h1 : IsIso (DerivedCategory.Qh.map s) := isIso_Qh_map_quotient_map_of_quasiIso p
  have h1' : IsIso ((DerivedCategory.Qh ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map s) :=
    inferInstanceAs (IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      f).map (DerivedCategory.Qh.map s)))
  have h2 : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).app ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P)) :=
    Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat f P hP
  have h3 : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy f).map
      s) := by
    have := quasiIso_modulePullback_map_of_stalkTorVanishing f hTor hP p
    exact isIso_Qh_map_quotient_map_of_quasiIso
      (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map p)
  have h4 : IsIso ((DerivedCategory.Qh ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map s ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ) 0).obj ℳ))) := by
    rw [(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      f).naturality s]
    infer_instance
  exact IsIso.of_isIso_comp_left ((DerivedCategory.Qh ⋙
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map s) _

end Stacks.Cohomology.PullbackSingleTor

end
