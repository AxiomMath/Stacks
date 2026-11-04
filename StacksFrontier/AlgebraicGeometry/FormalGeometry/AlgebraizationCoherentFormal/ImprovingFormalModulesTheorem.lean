module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesProIso
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Improving coherent formal modules (Stacks, Tag 0EJE)

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with quasi-coherent ideal sheaf `ℐ`,
`(ℱ_n)` an object of `Coh(X, ℐ)` and `T ⊆ Y` a subset stable under specialization. Assume that
for `y ∈ T` and every nonmaximal prime `𝔭 ⊆ 𝒪_{X,y}^∧` with `V(𝔭) ∩ V(ℐ_y^∧) = {𝔪_y^∧}` the
localization `(ℱ_y^∧)_𝔭` has positive depth. Then the canonical map `(ℱ_n) → (ℱ'_n)` dividing
each term by its sections supported in `T` satisfies:

1. `depth(ℱ'_{n,y}) ≥ 1` for `y ∈ T`;
2. `(ℱ'_n)` is isomorphic as a pro-system to an object `(𝒢_n)` of `Coh(X, ℐ)`;
3. the induced morphism `(ℱ_n) → (𝒢_n)` of `Coh(X, ℐ)` is surjective with kernel annihilated by
   a power of `ℐ`.

The source assumes in addition that `X` locally has a dualizing complex. The proof here does not
use it: the essential constancy of the sections supported in `T` of the levels (the case `s = 0`
of Stacks, Tag 0EIE) is proved from the depth condition by an associated-prime argument on the
completed stalks (`Stacks.LocalCohomology.FormalFiltration.exists_forall_pow_smul_mem_imp_mem`),
made uniform by a minimal-prime induction
(`Stacks.LocalCohomology.exists_forall_sectionsWithSupportIn_map_eq_zero`) and a finite affine
cover.

## Main results

* `Stacks.Algebraization.exists_proIso_coherentAdicSystem_toImprovedSystem` — **Stacks 0EJE**.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (F : Stacks.Coherent.CoherentAdicSystems I) (T : Set X) (hT : StableUnderSpecialization T)

/-- **Stacks Project, Tag 0EJE.** Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of
ideals with closed subscheme `Y`, `(ℱ_n)` an object of `Coh(X, ℐ)` and `T ⊆ Y` stable under
specialization. Assume that for `y ∈ T` and every nonmaximal prime `𝔭` of `𝒪_{X,y}^∧` with
`V(𝔭) ∩ V(ℐ𝒪_{X,y}^∧) = {𝔪_y^∧}` the module `(ℱ_y^∧)_𝔭` has positive depth. Then the canonical
map `(ℱ_n) → (ℱ'_n)` onto the quotients by the sections supported in `T`
(`Stacks.Algebraization.toImprovedSystem`, each component the depth-one quotient of Stacks,
Tag 0DX3: `ℱ'_n` coherent, the map surjective and an isomorphism on stalks outside `T`) has the
following properties:

1. every `ℱ'_n` has depth at least one at every point of `T`;
2. `(ℱ'_n)` is isomorphic as a pro-system to an object `(𝒢_n)` of `Coh(X, ℐ)`: there is a
   pro-isomorphism `P` whose forward maps are the components of a morphism
   `ψ : (𝒢_n) → (ℱ'_n)`;
3. the induced morphism `φ : (ℱ_n) → (𝒢_n)` of `Coh(X, ℐ)`, the one with `φ ≫ ψ` the canonical
   map, is an epimorphism of `Coh(X, ℐ)` whose kernel in `Coh(X, ℐ)` is annihilated by a power of
   `ℐ`.

The source also assumes that `X` locally has a dualizing complex; the statement holds without
it. -/
@[stacks 0EJE "the canonical map (ℱₙ) → (ℱ'ₙ) and its properties (1), (2) and (3); stated for every
Noetherian scheme, without the dualizing complex of the source"]
theorem exists_proIso_coherentAdicSystem_toImprovedSystem (hTY : T ⊆ I.support)
    (h6 : ∀ y ∈ T, ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p) :
    (∀ n : ℕᵒᵖ, IsDepthOneQuotient T ((toImprovedSystem T hT F.obj).app n)) ∧
    (∀ (n : ℕ) (y : X), y ∈ T →
      letI : Module (X.presheaf.stalk y) (TopCat.Presheaf.stalk (C := Ab.{u})
          ((improvedSystem T hT F.obj).obj (op n)).val.presheaf y) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) ((improvedSystem T hT F.obj).obj (op n)).val y
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
        (TopCat.Presheaf.stalk (C := Ab.{u}) ((improvedSystem T hT F.obj).obj (op n)).val.presheaf
          y)) ∧
    ∃ (G : Stacks.Coherent.CoherentAdicSystems I) (φ : F ⟶ G)
      (ψ : G.obj ⟶ improvedSystem T hT F.obj)
      (P : InverseSequence.ProIso G.obj (improvedSystem T hT F.obj)),
      φ.hom ≫ ψ = toImprovedSystem T hT F.obj ∧
      (∀ m, P.φ m = InverseSequence.tr G.obj (P.αle m) ≫ ψ.app (op m)) ∧
      Epi φ ∧
      ∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((kernel φ).obj.obj (op n)) = ⊥ := by
  obtain ⟨μ, hμ, hμmono, G, φ, ψ, π, hφψ, hπψ, hπnat, hψπ, hepi, c, hker⟩ :=
    exists_coherentAdicSystem_improvement F T hT hTY h6
  let P : InverseSequence.ProIso G.obj (improvedSystem T hT F.obj) :=
    { α := id
      β := μ
      αmono := monotone_id
      βmono := hμmono
      αle := fun _ => le_rfl
      βle := hμ
      φ := fun m => ψ.app (op m)
      ψ := π
      φnat := fun h => ψ.naturality (homOfLE h).op
      ψnat := fun h => hπnat h
      ψφ := fun m => hψπ m
      φψ := fun m => hπψ m }
  refine ⟨isDepthOneQuotient_toImprovedSystem_app T hT F.obj,
    fun n y hy => one_le_depth_improvedSystem_stalk T hT F.obj (op n) y hy,
    G, φ, ψ, P, hφψ, fun m => ?_, hepi, c, hker⟩
  exact (Category.id_comp _).symm.trans
    (congrArg (fun k => k ≫ ψ.app (op m)) (InverseSequence.ProIso.tr_refl G.obj le_rfl).symm)

end Stacks.Algebraization

end
