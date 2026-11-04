module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Modules.AffinePullbackCentral
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.CategoryTheory.Functor.DescentOfMaps

/-!
# Morphisms of quasi-coherent modules descend along every comparison

For a cofiltered diagram `D` of schemes with affine transition morphisms, an affine limit `c` and
an affine stage `D.obj i`, a morphism between the inverse images to `c.pt` of two quasi-coherent
modules of finite presentation on `D.obj i` is, at a later stage `e : j ⟶ i`, the inverse image of
a morphism over `D.obj j`, read through *any* isomorphism
`pullbackQcoh (D.map e) ⋙ pullbackQcoh (c.π.app j) ≅ pullbackQcoh (c.π.app i)`
(Stacks 01ZR (2); two comparisons differ by a central automorphism). The two other clauses of
Stacks 01ZR are recorded in the same language of quasi-coherent full subcategories, for a
quasi-compact (and quasi-separated) stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

open _root_.AlgebraicGeometry

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **Stacks 01ZR (2), for any comparison of iterated inverse images.** With an affine limit and
an affine stage, a morphism between inverse images to the limit of quasi-coherent modules of finite
presentation descends to a later stage, along every comparison isomorphism. -/
theorem exists_descendsAlong_pullbackQcoh_of_isLimit (hc : IsLimit c) (i : I) [IsAffine c.pt]
    [IsAffine (D.obj i)]
    (M N : (SheafOfModules.isQuasicoherent (D.obj i).ringCatSheaf).FullSubcategory)
    [M.obj.IsFinitePresentation] [N.obj.IsFinitePresentation]
    (φ : (Stacks.Modules.pullbackQcoh (c.π.app i)).obj M ⟶
      (Stacks.Modules.pullbackQcoh (c.π.app i)).obj N) :
    ∃ (j : I) (e : j ⟶ i),
      ∀ κ : Stacks.Modules.pullbackQcoh (D.map e) ⋙ Stacks.Modules.pullbackQcoh (c.π.app j) ≅
          Stacks.Modules.pullbackQcoh (c.π.app i),
        Functor.DescendsAlong κ φ := by
  obtain ⟨j, e, φj, hφj⟩ := exists_map_of_pullback_of_isLimit D c hc i M.obj N.obj φ.hom
  refine ⟨j, e, fun κ => ?_⟩
  let κ₀ : Stacks.Modules.pullbackQcoh (D.map e) ⋙ Stacks.Modules.pullbackQcoh (c.π.app j) ≅
      Stacks.Modules.pullbackQcoh (c.π.app i) :=
    NatIso.ofComponents (fun X => ObjectProperty.isoMk _
        ((Scheme.Modules.pullbackComp (c.π.app j) (D.map e) ≪≫
          Scheme.Modules.pullbackCongr (c.w e)).app X.obj))
      (fun f => ObjectProperty.hom_ext _
        ((Scheme.Modules.pullbackComp (c.π.app j) (D.map e) ≪≫
          Scheme.Modules.pullbackCongr (c.w e)).hom.naturality f.hom))
  have h₀ : Functor.DescendsAlong κ₀ φ :=
    ⟨ObjectProperty.homMk φj, ObjectProperty.hom_ext _ hφj⟩
  exact h₀.of_natEndCentral (Functor.NatEndCentral.of_comp_faithful (d := ObjectProperty.ι _)
    (Scheme.Modules.natEndCentral_pullback_of_isAffine (X := c.pt) (Y := D.obj i) (c.π.app i))) κ

/-- **Stacks 01ZR (1)**, on quasi-coherent full subcategories: a quasi-coherent module of finite
presentation on the limit is the inverse image of one on a stage. -/
theorem exists_pullbackQcoh_iso_of_isLimit (hc : IsLimit c)
    [∀ j : I, CompactSpace (D.obj j)] [∀ j : I, QuasiSeparatedSpace (D.obj j)]
    (N : (SheafOfModules.isQuasicoherent c.pt.ringCatSheaf).FullSubcategory)
    [N.obj.IsFinitePresentation] :
    ∃ (i : I) (M : (SheafOfModules.isQuasicoherent (D.obj i).ringCatSheaf).FullSubcategory),
      M.obj.IsFinitePresentation ∧
        Nonempty ((Stacks.Modules.pullbackQcoh (c.π.app i)).obj M ≅ N) := by
  obtain ⟨i, F, hF, ⟨e⟩⟩ := exists_isFinitePresentation_pullback_iso_of_qcqs D c hc N.obj
  exact ⟨i, ⟨F, Stacks.Modules.isQuasicoherent_of_isFinitePresentation F⟩, hF,
    ⟨ObjectProperty.isoMk _ e.symm⟩⟩

/-- **Stacks 01ZR (3)**, on quasi-coherent full subcategories: two morphisms of quasi-coherent
modules of finite presentation on a quasi-compact stage with equal inverse images to the limit
have equal inverse images to a later stage. -/
theorem exists_pullbackQcoh_map_eq_of_isLimit (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)]
    {M N : (SheafOfModules.isQuasicoherent (D.obj i).ringCatSheaf).FullSubcategory}
    [M.obj.IsFinitePresentation] [N.obj.IsFinitePresentation] (ψ₁ ψ₂ : M ⟶ N)
    (h : (Stacks.Modules.pullbackQcoh (c.π.app i)).map ψ₁ =
      (Stacks.Modules.pullbackQcoh (c.π.app i)).map ψ₂) :
    ∃ (j : I) (e : j ⟶ i), (Stacks.Modules.pullbackQcoh (D.map e)).map ψ₁ =
      (Stacks.Modules.pullbackQcoh (D.map e)).map ψ₂ := by
  obtain ⟨j, e, he⟩ := exists_pullback_map_eq_of_isLimit' D c hc i M.obj N.obj ψ₁.hom ψ₂.hom
    (congrArg (fun f => f.hom) h)
  exact ⟨j, e, ObjectProperty.hom_ext _ he⟩

end Stacks.AlgebraicGeometry.ModuleLimits

end
