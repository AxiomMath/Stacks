module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitClauseTransfer

/-!
# The three clauses of Stacks 01ZR as a pullback system of Zariski modules

Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact and quasi-separated schemes
with affine transition morphisms.  Stacks 01ZR says that the category of finitely presented
modules on `c.pt` is the colimit of the categories of finitely presented modules on the stages.
This file packages the inverse images of Zariski modules along `D` and along the projections of
`c` as a `Stacks.ModuleColimit.PullbackSystem`, and reads the three clauses of Stacks 01ZR — as
proved in `StacksFrontier/AlgebraicGeometry/ModuleLimits/` — as its three clauses.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.zariskiPullbackSystem`: the pullback system of Zariski
  modules of finite presentation over `D` and `c`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.zariskiPullbackSystem_faithfulness`,
  `.zariskiPullbackSystem_fullness` and `.zariskiPullbackSystem_essSurj`: the three clauses of
  Stacks 01ZR in that language.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- **The pullback system of Zariski modules over a cone of schemes.**  The category at a stage is
the category of `𝒪`-modules of the stage, the category over the limit that of the vertex of the
cone, the inverse images are `AlgebraicGeometry.Scheme.Modules.pullback`, the comparison is the
composition comparison followed by the transport along the commutation of the cone, and the
property of objects is finite presentation. -/
abbrev zariskiPullbackSystem : Stacks.ModuleColimit.PullbackSystem.{u, u, u, u + 1} I where
  C j := (D.obj j).Modules
  L := c.pt.Modules
  pb e := Scheme.Modules.pullback (D.map e)
  pbL j := Scheme.Modules.pullback (c.π.app j)
  comp {j _k} e := (Scheme.Modules.pullbackComp (c.π.app j) (D.map e) ≪≫
    Scheme.Modules.pullbackCongr (c.w e)).symm
  P _ M := M.IsFinitePresentation
  PL M := M.IsFinitePresentation

variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- **Stacks 01ZR (3)**, the faithfulness clause, for the Zariski pullback system. -/
theorem zariskiPullbackSystem_faithfulness (hc : IsLimit c) :
    (zariskiPullbackSystem D c).Faithfulness := by
  intro k M N hM hN φ ψ h
  have : M.IsFinitePresentation := hM
  have : N.IsFinitePresentation := hN
  exact exists_pullback_map_eq_of_isLimit D c hc k M N φ ψ h

/-- **Stacks 01ZR (2)**, the fullness clause, for the Zariski pullback system. -/
theorem zariskiPullbackSystem_fullness (hc : IsLimit c) :
    (zariskiPullbackSystem D c).Fullness := by
  intro k M N hM hN φ
  have : M.IsFinitePresentation := hM
  have : N.IsFinitePresentation := hN
  obtain ⟨j, e, φj, h⟩ := exists_map_of_pullback_of_isLimit D c hc k M N φ
  refine ⟨j, e, φj, ?_⟩
  show (Scheme.Modules.pullback (c.π.app j)).map φj =
    ((Scheme.Modules.pullbackComp (c.π.app j) (D.map e)).hom.app M ≫
      (Scheme.Modules.pullbackCongr (c.w e)).hom.app M) ≫ φ ≫
      ((Scheme.Modules.pullbackCongr (c.w e)).inv.app N ≫
        (Scheme.Modules.pullbackComp (c.π.app j) (D.map e)).inv.app N)
  have h' := congrArg (fun t => t ≫ (Scheme.Modules.pullbackCongr (c.w e)).inv.app N ≫
    (Scheme.Modules.pullbackComp (c.π.app j) (D.map e)).inv.app N) h
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app] at h'
  dsimp only [Functor.comp_obj] at h'
  simp only [Category.comp_id] at h'
  rw [h']
  simp only [Category.assoc]

/-- **Stacks 01ZR (1)**, the essential surjectivity clause, for the Zariski pullback system. -/
theorem zariskiPullbackSystem_essSurj (hc : IsLimit c) :
    (zariskiPullbackSystem D c).EssSurj := by
  intro M hM
  have : M.IsFinitePresentation := hM
  obtain ⟨i, Mi, hMi, ⟨e⟩⟩ := exists_isFinitePresentation_pullback_iso_of_qcqs D c hc M
  exact ⟨i, Mi, hMi, ⟨e.symm⟩⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
