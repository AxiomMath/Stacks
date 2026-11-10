module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleAdjunction

/-!
# Restriction along a surjective étale morphism is faithful

Let `j : U ⟶ X` be a surjective étale morphism. For every `W` étale over `X` the projection
`W ×_X U ⟶ W` is a covering of `W`, and a section of a sheaf over `W` is determined by its
restriction to `W ×_X U`, which is a section of the restriction `j^{-1}G` over the `U`-scheme
`W ×_X U`. Hence `j^{-1}` is faithful on sheaves of modules.

For a finite étale surjective `π : Y ⟶ X`, with `π_* ⊣ π^{-1}`, faithfulness of `π^{-1}` makes the
counit `π_* π^{-1} F ⟶ F` (the trace) an epimorphism.

## Main results

* `Stacks.EtaleCohomology.faithful_etaleModuleRestriction_of_surjective`
* `Stacks.EtaleCohomology.faithful_etaleModuleInverseImage_of_surjective`
* `Stacks.EtaleCohomology.epi_etaleModuleDirectImageInverseImageAdj_counit_app`: the trace
  `π_* π^{-1} F ⟶ F` of a finite étale surjective `π` is an epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type v) [Ring Λ] {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Restriction along a surjective étale morphism is faithful** on sheaves of modules. -/
theorem faithful_etaleModuleRestriction_of_surjective [Surjective j] :
    (etaleModuleRestriction.{u, v} Λ j).Faithful where
  map_injective {G G'} φ ψ h := by
    ext1
    refine NatTrans.ext (funext fun W => ?_)
    obtain ⟨W⟩ := W
    let Z : X.Etale := Scheme.Etale.mk (pullback.fst W.hom j ≫ W.hom)
    let f : Z ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom j) rfl
    have hcov : Sieve.ofArrows (fun _ : Unit => Z) (fun _ => f) ∈ X.smallEtaleTopology W := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      refine Set.eq_univ_of_forall fun w => Set.mem_iUnion.2 ⟨(), ?_⟩
      exact (Surjective.surj (f := pullback.fst W.hom j)) w
    refine G'.property.hom_ext_ofArrows (fun _ : Unit => f) hcov fun _ => ?_
    let Z' : U.Etale := Scheme.Etale.mk (pullback.snd W.hom j)
    let e : (Scheme.Etale.smallEtaleCompose j).obj Z' ≅ Z :=
      MorphismProperty.Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ (pullback.fst W.hom j ≫ W.hom) = pullback.snd W.hom j ≫ j
        rw [Category.id_comp, pullback.condition])
    have hZ : φ.hom.app (op ((Scheme.Etale.smallEtaleCompose j).obj Z')) =
        ψ.hom.app (op ((Scheme.Etale.smallEtaleCompose j).obj Z')) :=
      congrArg (fun χ => χ.hom.app (op Z')) h
    have key : φ.hom.app (op Z) = ψ.hom.app (op Z) := by
      rw [← cancel_mono (G'.obj.map e.hom.op), ← φ.hom.naturality e.hom.op,
        ← ψ.hom.naturality e.hom.op, hZ]
    rw [← φ.hom.naturality, ← ψ.hom.naturality, key]

/-- **Inverse image along a surjective étale morphism is faithful** on sheaves of modules. -/
theorem faithful_etaleModuleInverseImage_of_surjective [Surjective j] :
    (etaleModuleInverseImage.{u, v} Λ j).Faithful :=
  have := faithful_etaleModuleRestriction_of_surjective Λ j
  Functor.Faithful.of_iso (etaleModuleInverseImageRestrictionIso.{u, v} Λ j).symm

variable {Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Etale π] [Surjective π]

/-- **The trace of a finite étale surjective morphism is an epimorphism**: the counit
`π_* π^{-1} F ⟶ F` of `π_* ⊣ π^{-1}`, since `π^{-1}` is faithful. -/
theorem epi_etaleModuleDirectImageInverseImageAdj_counit_app (F : EtaleModules.{u, v} Λ X) :
    Epi ((etaleModuleDirectImageInverseImageAdj.{u, v} Λ π).counit.app F) :=
  have := faithful_etaleModuleInverseImage_of_surjective Λ π
  inferInstance

end Stacks.EtaleCohomology

end
