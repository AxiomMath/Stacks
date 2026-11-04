module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Descend

/-!
# Descent of finitely presented modules from morphisms descended up to isomorphism

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `c` be a limit cone on it. This file proves that every finitely presented
module on `c.pt` is the pullback of a finitely presented module on some stage
([Stacks Project, Tag 01ZR] (1)) from two inputs: that the counit of `pullback ⊣ pushforward`
along an affine morphism is an epimorphism at quasi-coherent modules, and descent of morphisms
([Stacks Project, Tag 01ZR] (2)) in a form where the descended morphism `φj` is compatible with
`φ` through *some* pair of isomorphisms, not necessarily the canonical comparisons
`pullbackComp` and `pullbackCongr`. This generalizes
`exists_isFinitePresentation_pullback_iso_of_inputs`, which asks for the canonical comparisons.

## Main results

* `exists_isFinitePresentation_pullback_iso_of_upToIso_inputs`, in the namespace
  `Stacks.AlgebraicGeometry.ModuleLimits`: Tag 01ZR (1) in the quasi-compact quasi-separated
  case, from descent of morphisms up to an arbitrary identification.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open Scheme.Modules

/- `AlgebraicGeometry.Scheme.Modules` carries its own `Category` instance whose `Hom` field is a
separate definition, so instance search does not transport facts about colimits in
`SheafOfModules X.ringCatSheaf` to `X.Modules` unless these definitions are reducible. -/
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms and `c` a limit cone on it. Assume that the counit of
`pullback ⊣ pushforward` along an affine morphism is an epimorphism at quasi-coherent modules
(`hepi`), and that morphisms between pullbacks of finitely presented modules descend to some
stage, compatibly through *some* pair of isomorphisms (`hmap`, a form of
[Stacks Project, Tag 01ZR] (2)). Then every finitely presented module on `c.pt` is isomorphic to
the pullback of a finitely presented module on some stage ([Stacks Project, Tag 01ZR] (1)). -/
theorem exists_isFinitePresentation_pullback_iso_of_upToIso_inputs
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hepi : AffineCounitEpi.{u})
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
        (iF : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj F) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj F)
        (iG : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj G) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) := by
  classical
  let i : I := IsCofiltered.nonempty.some
  let f : c.pt ⟶ D.obj i := c.π.app i
  have hfa : IsAffineHom f := isAffineHom_π_app' D c hc i
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit' D c hc
  obtain ⟨G, _, p, _⟩ := exists_finitePresentation_epi_pullback hepi f F
  have hGp : ((Scheme.Modules.pullback f).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback f G
  have hkq : (kernel p).IsQuasicoherent := by
    let _ : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent :=
      Stacks.Modules.isQuasicoherent_pullback f G inferInstance
    infer_instance
  have hkt : (kernel p).IsFiniteType := by
    let _ := hGp
    exact Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType p
  obtain ⟨H, _, q, _⟩ := exists_finitePresentation_epi_pullback hepi f (kernel p)
  let φ := q ≫ kernel.ι p
  obtain ⟨j, e, φj, iH, iG, hφj⟩ := hmap i H G ‹_› ‹_› φ
  have hfp : (cokernel φj).IsFinitePresentation := by
    let _ := isFinitePresentation_pullback (D.map e) H
    let _ := isFinitePresentation_pullback (D.map e) G
    exact Stacks.SheafOfModules.isFinitePresentation_cokernel φj
  refine ⟨j, cokernel φj, hfp, ?_⟩
  let eC : cokernel ((Scheme.Modules.pullback (c.π.app j)).map φj) ≅ cokernel φ :=
    cokernel.mapIso _ _ iH iG hφj
  let hpC : IsColimit (CokernelCofork.ofπ p (kernel.condition p)) :=
    Abelian.epiIsCokernelOfKernel
      (KernelFork.ofι (kernel.ι p) (kernel.condition p)) (kernelIsKernel p)
  let eF : cokernel φ ≅ F :=
    cokernelEpiComp q (kernel.ι p) ≪≫
      (cokernelIsCokernel (kernel.ι p)).coconePointUniqueUpToIso hpC
  exact ⟨eF.symm ≪≫ eC.symm ≪≫
    (PreservesCokernel.iso (Scheme.Modules.pullback (c.π.app j)) φj).symm⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
