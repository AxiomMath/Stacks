module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationLeftDerived

/-!
# The cartesian object realizing a cartesian simplicial system of modules, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of commutative rings on
its total site and let `(K_n, K_φ)` be a cartesian simplicial system of the derived category of
modules (Stacks 0D9N) with `Hom(K_i[t], K_i) = 0` for `t > 0`. This file identifies the
restriction to each simplicial degree of the totalization of the realization complex
`n ↦ Lg_{n!}K_n` of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleRealizationLeftDerived.lean`
with the object of the system in that degree, and so proves the conclusion of Stacks 0D9T with
**no flatness hypothesis** on the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m`.

The source's hypothesis (1), flatness, is used there only to make `g_{n!}` exact; the left
derived lower shriek and its direct-sum formula,
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekLeftDerived` and
`CategoryTheory.SimplicialSiteSituation.isIso_derivedModuleSumComparison`, make it unnecessary.
This matters for the small étale site of an fppf hypercovering, whose degeneracy transitions are
not flat in general (see the module docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/SimplicialQuasicoherentDerivedGluing.lean`).

The mechanism is that of Stacks 0D9L: the restriction to degree `m` of the realization complex is
the alternating face map complex of the copower of `K_m` by the simplices of the standard simplex
on `m`, which carries an extra degeneracy, so it is contracted onto `K_m`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealization_component_iso`: the
  restriction of the totalization to degree `m` is `K_m`.
* `CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_realizing_moduleSystem`:
  **the conclusion of Stacks 0D9T without its flatness hypothesis.**

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

-- No global `HasDerivedCategory` instance exists for these module categories (checked with
-- `#synth`), so the standard model of the tower this file extends is installed locally.
attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_additive
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_commShift
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_isTriangulated

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.simplexCopower
  CategoryTheory.simplexCopowerAugmented
  CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealizationSimplicial
  CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealizationTerm

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology CommRingCat.{u}}

/-- **The comparison of the copower with the restriction of the realization, as an
isomorphism.** -/
noncomputable def leftDerivedModuleRealizationComponentComparisonIso
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopower (T.obj m) m ≅
      leftDerivedModuleRealizationSimplicial T hT ⋙ S.derivedComponentModuleRestriction O m :=
  letI := leftDerivedModuleRealizationComponentComparison_isIso T hT m
  asIso (leftDerivedModuleRealizationComponentComparison T hT m)

/-- **The restriction of the realization to a simplicial degree, augmented by the object of the
system.** The augmentation is the comparison with the copower followed by the augmentation of the
copower; this is the augmented simplicial object whose extra degeneracy contracts the restricted
realization complex. -/
noncomputable def leftDerivedModuleRealizationComponentAugmented
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    SimplicialObject.Augmented (DerivedCategory (S.componentRingedTopos O m).Modules) where
  left := leftDerivedModuleRealizationSimplicial T hT ⋙ S.derivedComponentModuleRestriction O m
  right := T.obj m
  hom := (leftDerivedModuleRealizationComponentComparisonIso T hT m).inv ≫
    (simplexCopowerAugmented (T.obj m) m).hom

/-- The comparison with the copower is an isomorphism of *augmented* simplicial objects. -/
noncomputable def leftDerivedModuleRealizationComponentAugmentedIso
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopowerAugmented (T.obj m) m ≅
      leftDerivedModuleRealizationComponentAugmented T hT m :=
  Comma.isoMk (leftDerivedModuleRealizationComponentComparisonIso T hT m) (Iso.refl _) (by
    dsimp only [leftDerivedModuleRealizationComponentAugmented, Functor.id_map, Iso.refl_hom]
    rw [Iso.hom_inv_id_assoc]
    simp)

/-- **The restriction of the realization to a simplicial degree carries an extra
degeneracy**, transported from the copower along the comparison of augmented simplicial
objects. -/
noncomputable def leftDerivedModuleRealizationComponentExtraDegeneracy
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    (leftDerivedModuleRealizationComponentAugmented T hT m).ExtraDegeneracy :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (leftDerivedModuleRealizationComponentAugmentedIso T hT m)
    (simplexCopowerExtraDegeneracy (T.obj m) m)

/-- The restriction of the differential of the realization complex is the alternating face map
differential of the restricted simplicial object. -/
theorem derivedComponentModuleRestriction_map_leftDerivedModuleRealizationComplex_d
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) (n : ℕ) :
    (S.derivedComponentModuleRestriction O m).map
        ((leftDerivedModuleRealizationComplex T hT).d (n + 1) n) =
      AlgebraicTopology.AlternatingFaceMapComplex.objD
        (leftDerivedModuleRealizationComponentAugmented T hT m).left n := by
  simp only [leftDerivedModuleRealizationComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
    SimplicialObject.δ, leftDerivedModuleRealizationComponentAugmented, Functor.comp_map]
  rfl

/-- The first identity of the contraction: the differential out of degree one kills the
augmentation. -/
theorem leftDerivedModuleRealizationComponent_d_comp_augmentation
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).map
          ((leftDerivedModuleRealizationComplex T hT).d (0 + 1) 0) ≫
        (leftDerivedModuleRealizationComponentAugmented T hT m).hom.app
          (Opposite.op ⦋0⦌) = 0 := by
  obtain ⟨hd₀, -, -⟩ := Triangulated.extraDegeneracy_contraction
    (leftDerivedModuleRealizationComponentAugmented T hT m)
    (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m)
  rw [derivedComponentModuleRestriction_map_leftDerivedModuleRealizationComplex_d T hT m 0]
  exact hd₀

/-- The second identity of the contraction, in degree zero. -/
theorem leftDerivedModuleRealizationComponent_augmentation_contraction
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    ((leftDerivedModuleRealizationComponentAugmented T hT m).hom.app (Opposite.op ⦋0⦌) ≫
            (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s' :
          (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋0⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋0⦌)) +
        ((leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s 0 ≫
            (S.derivedComponentModuleRestriction O m).map
              ((leftDerivedModuleRealizationComplex T hT).d (0 + 1) 0) :
          (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋0⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋0⦌)) = 𝟙 _ := by
  obtain ⟨-, hc₀, -⟩ := Triangulated.extraDegeneracy_contraction
    (leftDerivedModuleRealizationComponentAugmented T hT m)
    (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m)
  rw [← derivedComponentModuleRestriction_map_leftDerivedModuleRealizationComplex_d T hT m 0]
    at hc₀
  exact hc₀

/-- The third identity of the contraction: the extra degeneracy is a contracting homotopy for the
restricted realization complex in every positive degree. -/
theorem leftDerivedModuleRealizationComponent_contraction
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) (n : ℕ) :
    ((S.derivedComponentModuleRestriction O m).map
              ((leftDerivedModuleRealizationComplex T hT).d (n + 1) n) ≫
            (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s n :
          (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋n + 1⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋n + 1⦌)) +
        ((leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s (n + 1) ≫
            (S.derivedComponentModuleRestriction O m).map
              ((leftDerivedModuleRealizationComplex T hT).d (n + 1 + 1) (n + 1)) :
          (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋n + 1⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (leftDerivedModuleRealizationTerm S O T ⦋n + 1⦌)) = 𝟙 _ := by
  obtain ⟨-, -, hc'⟩ := Triangulated.extraDegeneracy_contraction
    (leftDerivedModuleRealizationComponentAugmented T hT m)
    (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m)
  have hc := hc' n
  rw [← derivedComponentModuleRestriction_map_leftDerivedModuleRealizationComplex_d T hT m n,
    ← derivedComponentModuleRestriction_map_leftDerivedModuleRealizationComplex_d T hT m (n + 1)]
    at hc
  exact hc

/-- **The positively shifted morphisms from a restricted term of the realization to the object of
the system vanish.** The restricted term is a coproduct of copies of that object, by the
comparison with the copower, and the source's hypothesis (3) kills each summand. -/
theorem leftDerivedModuleRealizationComponent_hom_zero
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (m : SimplexCategory) (n : ℕ)
    (f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
      ((n + 1 : ℕ) : ℤ)).obj ((S.derivedComponentModuleRestriction O m).obj
        (leftDerivedModuleRealizationTerm S O T ⦋n + 2⦌)) ⟶ T.obj m) : f = 0 := by
  let := derivedComponentModules_hasCountableCoproducts (S := S) (O := O) m
  let a := (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
      ((n + 1 : ℕ) : ℤ)).mapIso
        ((leftDerivedModuleRealizationComponentComparisonIso T hT m).app
          (Opposite.op ⦋n + 2⦌)).symm ≪≫
    Limits.PreservesCoproduct.iso (shiftFunctor
      (DerivedCategory (S.componentRingedTopos O m).Modules) ((n + 1 : ℕ) : ℤ))
      (fun _ : ⦋n + 2⦌ ⟶ m => T.obj m)
  refine hom_eq_zero_of_iso a (Iso.refl _) ?_ f
  intro g
  exact hom_eq_zero_of_coproduct
    (fun _ : ⦋n + 2⦌ ⟶ m =>
      (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
        ((n + 1 : ℕ) : ℤ)).obj (T.obj m))
    (fun _ => hHom m (n + 1) (by omega)) g

/-- The vertex component of the inverse comparison is a retraction of the transposed transition
out of degree zero: this is the identity the isomorphism of
`CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealization_component_iso` inherits. -/
theorem leftDerivedModuleRealizationComponentInclusion_comp_augmentation
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory)
    (ψ : ⦋0⦌ ⟶ m) :
    leftDerivedModuleRealizationComponentInclusion T hT ψ ≫
      (leftDerivedModuleRealizationComponentAugmented T hT m).hom.app
        (Opposite.op ⦋0⦌) = 𝟙 _ := by
  let e := leftDerivedModuleRealizationComponentComparisonIso T hT m
  show leftDerivedModuleRealizationComponentInclusion T hT ψ ≫ e.inv.app (Opposite.op ⦋0⦌) ≫
    Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ m => 𝟙 (T.obj m)) = 𝟙 _
  rw [← leftDerivedModuleRealizationComponentComparison_ι T hT ψ]
  show (Limits.Sigma.ι (fun _ : ⦋0⦌ ⟶ m => T.obj m) ψ ≫ e.hom.app (Opposite.op ⦋0⦌)) ≫
    e.inv.app (Opposite.op ⦋0⦌) ≫ Limits.Sigma.desc _ = _
  simp

/-- **The restriction of the totalization to a simplicial degree is the object of the system.**
The restriction to degree `m` of the module realization is, by the direct-sum formula and
cartesianness, the copower of the object of the system in degree `m` by the simplices of the
standard simplex on `m`; that copower is an augmented simplicial object with an extra degeneracy,
so its alternating face map complex is contracted onto the augmentation, and the totalization of a
contracted complex is its base. -/
theorem leftDerivedModuleRealization_component_iso
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (P : Triangulated.SequentialPostnikovSystem
      (fun n : ℕ => leftDerivedModuleRealizationTerm S O T ⦋n⦌)
      (fun n : ℕ => (leftDerivedModuleRealizationComplex T hT).d (n + 1) n))
    {K : DerivedCategory (S.totalRingedTopos O).Modules}
    (p : (letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      ∐ P.sequence.obj) ⟶ K)
    (q : K ⟶ (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (1 : ℤ)).obj
      (letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
        ∐ P.sequence.obj))
    (hK : letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      Triangle.mk (Triangulated.telescopeMap P.sequence) p q ∈
        distTriang (DerivedCategory (S.totalRingedTopos O).Modules))
    (i : leftDerivedModuleRealizationTerm S O T ⦋0⦌ ⟶ K)
    (hi : letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      P.π 0 ≫ i =
        (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app
          (P.obj 0) ≫ Limits.Sigma.ι P.sequence.obj 0 ≫ p)
    (m : SimplexCategory) :
    ∃ γ : (S.derivedComponentModuleRestriction O m).obj K ≅ T.obj m,
      ∀ ψ : ⦋0⦌ ⟶ m, leftDerivedModuleRealizationComponentInclusion T hT ψ ≫
        (S.derivedComponentModuleRestriction O m).map i ≫ γ.hom = 𝟙 _ := by
  let := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  let := derivedComponentModules_hasCountableCoproducts (S := S) (O := O) m
  let := derivedComponentModuleRestriction_preservesCountableCoproducts (S := S) (O := O) m
  obtain ⟨r, s, hr, hs, ht⟩ :=
    (P.map (S.derivedComponentModuleRestriction O m)).split_sequence (T.obj m)
      ((leftDerivedModuleRealizationComponentAugmented T hT m).hom.app (Opposite.op ⦋0⦌))
      (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s'
      (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s
      (leftDerivedModuleRealizationComponentExtraDegeneracy T hT m).s'_comp_ε
      (leftDerivedModuleRealizationComponent_d_comp_augmentation T hT m)
      (leftDerivedModuleRealizationComponent_augmentation_contraction T hT m)
      (leftDerivedModuleRealizationComponent_contraction T hT m)
      (leftDerivedModuleRealizationComponent_hom_zero T hT hHom m)
  obtain ⟨γ, hγ⟩ := Triangulated.exists_iso_of_split_restriction P
    (S.derivedComponentModuleRestriction O m) p q hK i hi (T.obj m)
    ((leftDerivedModuleRealizationComponentAugmented T hT m).hom.app (Opposite.op ⦋0⦌))
    r s hr hs ht
  refine ⟨γ, fun ψ => ?_⟩
  rw [hγ]
  exact leftDerivedModuleRealizationComponentInclusion_comp_augmentation T hT m ψ

/-- **The comparison of the restrictions of the totalization with the objects of the system is
compatible with the transitions out of degree zero.** The inverse of the comparison in degree `n`
is the transposed transition of the realization followed by the restriction of the degree-zero map
`i`, and the transpose of `i` itself is the map `β` that mediates every vertex square. -/
theorem leftDerivedModuleRealization_vertex_naturality (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {K : DerivedCategory (S.totalRingedTopos O).Modules}
    (i : leftDerivedModuleRealizationTerm S O T ⦋0⦌ ⟶ K)
    (γ : ∀ n, (S.derivedComponentModuleRestriction O n).obj K ≅ T.obj n)
    (hγ : ∀ (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n),
      leftDerivedModuleRealizationComponentInclusion T hT ψ ≫
        (S.derivedComponentModuleRestriction O n).map i ≫ (γ n).hom = 𝟙 _)
    (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
    T.map ψ ≫ (γ n).inv =
      (S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋0⦌).homEquiv _ _ i) ≫
        (S.derivedComponentModuleTransition O ψ).app K := by
  have := hT ψ
  have h : (γ n).inv = leftDerivedModuleRealizationComponentInclusion T hT ψ ≫
      (S.derivedComponentModuleRestriction O n).map i := by
    refine (cancel_mono (γ n).hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id] using (hγ n ψ).symm
  rw [h]
  simp only [leftDerivedModuleRealizationComponentInclusion]
  rw [leftDerivedModuleRealizationTermMap_homEquiv]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← (S.derivedComponentModuleTransition O ψ).naturality i]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rfl

/-- **Stacks 0D9T without its flatness hypothesis.** In a simplicial-site situation (Stacks 09WE,
either case) let `O` be a sheaf of rings on the total site and let `(K_n, K_φ)` be a simplicial
system of the derived category of modules which is cartesian and satisfies `Hom(K_i[t], K_i) = 0`
for all `i` and all `t > 0`. Then there is a cartesian object `K` of `D(O)` whose associated
simplicial system (Stacks 0D9P) is isomorphic to `(K_n, K_φ)`. No flatness of the structure-sheaf
transitions `f_φ^{-1}O_n ⟶ O_m` is assumed: the source's hypothesis (1) is replaced by the left
derived lower shriek.

The object is the totalization of the complex `n ↦ Lg_{n!}K_n`; its restriction to degree `m` is
`K_m` by `CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealization_component_iso`, the
comparisons being mediated at the vertices by the transpose of the degree-zero map into the
totalization, and cartesianness upgrades that to compatibility with every simplex map. -/
theorem exists_isCartesianDerivedModule_realizing_moduleSystem
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ K : DerivedCategory (S.totalRingedTopos O).Modules,
      S.IsCartesianDerivedModule O K ∧ Nonempty (T ≅ S.derivedModuleSystem O K) := by
  let := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  obtain ⟨P, K, p, q, hp⟩ := exists_leftDerivedModuleRealization T hT hHom
  have := P.isIso_π_zero
  let i : leftDerivedModuleRealizationTerm S O T ⦋0⦌ ⟶ K := inv (P.π 0) ≫
    (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app (P.obj 0) ≫
      Limits.Sigma.ι P.sequence.obj 0 ≫ p
  have hi : P.π 0 ≫ i =
      (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app (P.obj 0) ≫
        Limits.Sigma.ι P.sequence.obj 0 ≫ p := by
    simp [i]
  choose γ hγ using fun m =>
    leftDerivedModuleRealization_component_iso T hT hHom P p q hp i hi m
  let γ' (n : SimplexCategory) : T.obj n ≅ (S.derivedModuleSystem O K).obj n := (γ n).symm
  have hv (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
      T.map ψ ≫ (γ' n).hom =
        (S.derivedTransitionPullback O ψ).map
            ((S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋0⦌).homEquiv _ _ i) ≫
          (S.derivedModuleSystem O K).map ψ :=
    leftDerivedModuleRealization_vertex_naturality T hT i γ hγ n ψ
  have hn {m n : SimplexCategory} (φ : m ⟶ n) :
      T.map φ ≫ (γ' n).hom =
        (S.derivedTransitionPullback O φ).map (γ' m).hom ≫
          (S.derivedModuleSystem O K).map φ :=
    S.moduleSystem_naturality_of_vertex_compatibility O T (S.derivedModuleSystem O K) hT
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O ⦋0⦌).homEquiv _ _ i) γ' hv φ
  refine ⟨K, S.isCartesianDerivedModule_of_derivedModuleSystem_cartesian O K
    (S.moduleSystem_cartesian_of_iso O T (S.derivedModuleSystem O K) hT γ'
      (fun {_ _} φ => hn φ)), ⟨?_⟩⟩
  exact SimplicialDerivedModuleSystem.isoMk T (S.derivedModuleSystem O K) γ'
    (fun {_ _} φ => hn φ)

end CategoryTheory.SimplicialSiteSituation

end
