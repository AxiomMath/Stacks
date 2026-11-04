module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition

/-!
# From a degreewise comparison to a cartesian object of `D(O)`

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of commutative rings on
its total site and let `(K_n, K_φ)` be a simplicial system of the derived category of modules in
the sense of Stacks 0D9N. Stacks 0D9T asserts that a cartesian such system whose objects have no
positively shifted self-maps, over flat structure-sheaf transitions, is the system associated with
a cartesian object of `D(O)`.

This file proves the lemmas of the last step of that argument. Suppose an object `K` of `D(O)` is
given together with isomorphisms `γ_n : K_n ≅ Lg_n^* K` in every simplicial degree which are
compatible with the transitions out of degree zero, in the sense that a single map
`β : K_0 ⟶ Lg_0^* K` mediates all of them. Then cartesianness of the system alone forces the `γ_n`
to be compatible with *every* simplex map, hence to assemble into an isomorphism of simplicial
systems, and forces `K` to be a cartesian object of `D(O)`. The mechanism is that every simplex map
`φ : m ⟶ n` is preceded by a vertex `ψ : ⦋0⦌ ⟶ m`, along which the system's transition is
invertible; the cocycle condition then reduces the square for `φ` to the squares for `ψ` and
`ψ ≫ φ`. Stacks 0D9T itself is
`CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleSystem_naturality_of_vertex_compatibility`: a
  degreewise comparison of simplicial systems of the derived category of modules which is
  compatible with the transitions out of degree zero is compatible with every simplex map, as
  soon as the source system is cartesian.
* `CategoryTheory.SimplicialSiteSituation.moduleSystem_cartesian_of_iso`: a simplicial system of
  the derived category of modules isomorphic to a cartesian one is cartesian.
* `SimplicialSiteSituation.isCartesianDerivedModule_of_derivedModuleSystem_cartesian` is the
  converse of the second half of Stacks 0D9P — an object of `D(O)` whose associated simplicial
  system is cartesian is a cartesian object.

## Implementation notes

*Why the canonical compositor need not be inverted.* The abelian-sheaf analogue of the first
result,
`CategoryTheory.SimplicialSiteSituation.naturality_of_vertex_compatibility` of
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedOfSystem.lean`, cancels the
compositor of inverse images, which there is an isomorphism of exact functors. For modules the
canonical comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` is invertible only by Stacks 0D6D. It is
not cancelled here: both sides of the square for `φ`, after composing with the invertible
`Lf_φ^*(K_ψ)`, are rewritten by the cocycle condition into a composite *beginning* with the
comparison, so only its naturality in the object is used. Nothing in this file needs Stacks 0D6D.

*The vertex is the constant map.* `SimplexCategory.const` supplies `ψ : ⦋0⦌ ⟶ m` for every `m`,
which is what makes the reduction to degree zero available in every degree at once.

*The shape of the carried hypothesis.* The degreewise comparison is carried in exactly the shape
the realization of Stacks 0D9L produces it — a single map out of the degree-zero object together
with degreewise isomorphisms satisfying the vertex squares — so that the first result is the
interface a module-coefficient realization would plug into, and not an arbitrary assumption.

## What is not proved

The *existence* of the object `K` is not proved here, and that is where the source's hypotheses
(1), flatness of `f_φ^{-1}O_n ⟶ O_m`, and (3), the vanishing of `Hom(K_i[t], K_i)` for `t > 0`,
are used; they are therefore absent from the statements below rather than carried unused. It is
proved in `CartesianDerivedModuleOfModuleSystem.lean`, cited above.

## References

* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **A comparison compatible at the vertices is compatible everywhere.** Let `T` and `V` be
simplicial systems of the derived category of modules, let `β : T_0 ⟶ V_0` be a map in degree
zero and let `γ_n : T_n ≅ V_n` be isomorphisms whose squares against the transitions out of
degree zero are mediated by `β`. If `T` is cartesian then the `γ_n` satisfy the square against
every simplex map.

Every `φ : m ⟶ n` is preceded by the vertex `ψ : ⦋0⦌ ⟶ m`, whose transition `T_ψ` is invertible,
so it suffices to compare the two sides after composing with `Lf_φ^*(T_ψ)`. The cocycle condition
turns each of them into the canonical comparison `Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*` followed by a
side of the square for `ψ ≫ φ`; only the naturality of that comparison is used, not its
invertibility. -/
theorem moduleSystem_naturality_of_vertex_compatibility
    (T V : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (β : T.obj ⦋0⦌ ⟶ V.obj ⦋0⦌) (γ : ∀ n, T.obj n ≅ V.obj n)
    (hγ : ∀ (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n),
      T.map ψ ≫ (γ n).hom = (S.derivedTransitionPullback O ψ).map β ≫ V.map ψ)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    T.map φ ≫ (γ n).hom =
      (S.derivedTransitionPullback O φ).map (γ m).hom ≫ V.map φ := by
  let ψ : ⦋0⦌ ⟶ m := SimplexCategory.const _ _ 0
  have hψ : IsIso (T.map ψ) := hT ψ
  refine (cancel_epi ((S.derivedTransitionPullback O φ).map (T.map ψ))).1 ?_
  have hleft : (S.derivedTransitionPullback O φ).map (T.map ψ) ≫ T.map φ ≫ (γ n).hom =
      (S.derivedTransitionCompComparison O ψ φ).app (T.obj ⦋0⦌) ≫
        T.map (ψ ≫ φ) ≫ (γ n).hom := by
    rw [← Category.assoc, ← T.map_comp ψ φ, Category.assoc]
  have hnat := (S.derivedTransitionCompComparison O ψ φ).naturality β
  simp only [Functor.comp_map] at hnat
  have hright : (S.derivedTransitionPullback O φ).map (T.map ψ) ≫
        (S.derivedTransitionPullback O φ).map (γ m).hom ≫ V.map φ =
      (S.derivedTransitionCompComparison O ψ φ).app (T.obj ⦋0⦌) ≫
        T.map (ψ ≫ φ) ≫ (γ n).hom := by
    rw [← Functor.map_comp_assoc, hγ m ψ, Functor.map_comp, Category.assoc,
      ← V.map_comp ψ φ, ← Category.assoc, hnat, Category.assoc, hγ n (ψ ≫ φ)]
  exact hleft.trans hright.symm

/-- **A system isomorphic to a cartesian system is cartesian.** If the degreewise isomorphisms
`γ_n : T_n ≅ V_n` satisfy the square against every simplex map and `T` is cartesian, then every
transition of `V` is the composite of `Lf_φ^*(γ_m^{-1})`, the transition of `T` and `γ_n`. -/
theorem moduleSystem_cartesian_of_iso (T V : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) (γ : ∀ n, T.obj n ≅ V.obj n)
    (hγ : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), T.map φ ≫ (γ n).hom =
      (S.derivedTransitionPullback O φ).map (γ m).hom ≫ V.map φ) :
    V.Cartesian := by
  intro m n φ
  have hφ : IsIso (T.map φ) := hT φ
  have h : V.map φ =
      (S.derivedTransitionPullback O φ).map (γ m).inv ≫ T.map φ ≫ (γ n).hom := by
    rw [hγ φ, ← Functor.map_comp_assoc]
    simp
  rw [h]
  infer_instance

/-- **The converse of the second half of Stacks 0D9P.** An object of the derived category of
`O`-modules on the total site whose associated simplicial system of Stacks 0D9P is cartesian is
a cartesian object: the transitions of that system are the derived transitions of the object. -/
theorem isCartesianDerivedModule_of_derivedModuleSystem_cartesian
    (K : DerivedCategory (S.totalRingedTopos O).Modules)
    (hK : (S.derivedModuleSystem O K).Cartesian) :
    S.IsCartesianDerivedModule O K :=
  fun {_ _} φ => hK φ

end CategoryTheory.SimplicialSiteSituation

end
