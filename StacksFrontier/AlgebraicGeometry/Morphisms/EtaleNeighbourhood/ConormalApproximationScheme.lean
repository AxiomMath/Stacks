module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximation

/-!
# Controlling the conormal algebra of a closed fibre after completion

Let `Y → T → S` be finite type morphisms of Noetherian schemes, let `t ∈ T` lie over `s ∈ S` and
let `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a local `𝒪_{S,s}`-algebra map. Write `Y_σ` for the base change
of `Y → T` along `Spec(𝒪_{S,s}^∧) → T` determined by `σ`. Since `σ` exists, the residue fields of
`s` and `t` agree, so the fibre `Y_t` of `Y → T` at `t` is a closed subscheme of `Y_σ`. Assuming
`HasUniformConormalBound`, we show that a pointed finite type extension `(T', t') → (T, t)`
through which `σ` factors can be chosen so that every `σ'` factoring through it gives
`Y_t ↪ Y_{σ'}` with conormal algebra isomorphic to that of `Y_t ↪ Y_σ`.

## Main results

* `Stacks.ConormalApproximation.exists_finiteType_pointed_extension_conormalAlgebra_iso`: the
  conclusion of [Stacks, Tag 0CAY], under the hypothesis `HasUniformConormalBound`, which fails
  in general (`Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`).

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
* [Stacks Project, Tag 0CAX](https://stacks.math.columbia.edu/tag/0CAX)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.ConormalApproximation

/-- Let `p : Y ⟶ T` and `f : T ⟶ S` be finite type morphisms of Noetherian schemes, let `t ∈ T`
lie over `s ∈ S`, and let `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a local `𝒪_{S,s}`-algebra map. Assume
`HasUniformConormalBound p s t`: a single `N` such that any two such maps congruent modulo `𝔪_s^N`
give isomorphic conormal algebras. Then there is a finite type morphism `(T', t') → (T, t)`
through which `σ` factors such that every local `𝒪_{S,s}`-algebra map
`σ' : 𝒪_{T,t} → 𝒪_{S,s}^∧` factoring through `𝒪_{T',t'}` gives `Y_σ ← Y_t → Y_{σ'}` with
isomorphic conormal algebras.

The hypothesis `HasUniformConormalBound` fails in general: see
`Stacks.ConormalApproximation.not_exists_uniform_congruence_bound`. -/
theorem exists_finiteType_pointed_extension_conormalAlgebra_iso
    {S T Y : Scheme.{u}} (f : T ⟶ S) (p : Y ⟶ T)
    [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (s : S) (t : T) (ht : f t = s)
    (sigma : T.presheaf.stalk t →+* completedStalk S s)
    (hsigma : IsLocalHom sigma)
    (hsigma_base :
      sigma.comp ((f.stalkMap t).hom.comp
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
        algebraMap (S.presheaf.stalk s) (completedStalk S s))
    (hcompare : HasUniformConormalBound p s t) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g),
      ∃ tau : T'.presheaf.stalk t' →+* completedStalk S s,
        IsLocalHom tau ∧
        sigma = tau.comp ((g.stalkMap t').hom.comp
          (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom) ∧
        ∀ sigma' : T.presheaf.stalk t →+* completedStalk S s,
          IsLocalHom sigma' →
          sigma'.comp ((f.stalkMap t).hom.comp
            (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) ht).symm).hom) =
            algebraMap (S.presheaf.stalk s) (completedStalk S s) →
          (∃ tau' : T'.presheaf.stalk t' →+* completedStalk S s,
            sigma' = tau'.comp ((g.stalkMap t').hom.comp
              (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hgt).symm).hom)) →
          HasIsoConormalFibreImmersions p t
            (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
            (Spec.map (CommRingCat.ofHom sigma') ≫ T.fromSpecStalk t) := by
  obtain ⟨N, hN, hcomp⟩ := hcompare
  obtain ⟨T', g, t', hgt, hgft, hgqc, tau, htau, hfact, -, hagree⟩ :=
    AlgebraicGeometry.exists_finiteType_pointed_extension_agree_mod_maximalIdeal_pow
      f s t ht sigma hsigma hsigma_base N hN
  exact ⟨T', g, t', hgt, hgft, hgqc, tau, htau, hfact, fun sigma' hsigma' hsigma'_base hfactors ↦
    ⟨hasFibreImmersion_of_isLocalHom f p s t ht sigma hsigma hsigma_base,
      hasFibreImmersion_of_isLocalHom f p s t ht sigma' hsigma' hsigma'_base,
      hcomp sigma sigma' (hagree sigma' hsigma' hsigma'_base hfactors)⟩⟩

end Stacks.ConormalApproximation

end
