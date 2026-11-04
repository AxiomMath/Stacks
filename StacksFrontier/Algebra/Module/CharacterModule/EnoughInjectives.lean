module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.Topology.Instances.AddCircle.Defs
public import StacksFrontier.Algebra.Module.CharacterModule.Duality
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic

/-!
# Enough injectives for modules, via character modules

Let `R` be a commutative ring. For an `R`-module `M` write `M^∨ = Hom_ℤ(M, ℚ/ℤ)` for its
character module and `F(N) = ⨁_{n ∈ N} R[n]` for the free `R`-module on the underlying set of
`N`, with its natural surjection `F(N) → N`. Set

`J(M) = (F(M^∨))^∨`.

This file builds the free-module cover, proves that `J(M)` is injective, and assembles the
canonical maps `M → J(M)` into a functor `M ↦ (M → J(M))` from `R`-modules to arrows of
`R`-modules whose components are monomorphisms with injective targets. That is exactly the
Stacks Tag 0139 notion of functorial injective embeddings, so the category of `R`-modules has
enough injectives.

The character-dual functor itself, and its exactness, are in
`StacksFrontier.Algebra.Module.CharacterModule.Duality`.

## Main definitions

* `freeSurj`: the natural surjection `F(M) → M`.
* `freeModuleCoverFunctor`: the functor sending `M` to the epimorphism `F(M) → M`.
* `JModule`: the module `J(M) = (F(M^∨))^∨`.
* `jModuleEmbedding`: the canonical map `M → J(M)`.
* `jModuleFunctor`, `jModuleEmbeddingNatTrans`, `jModuleArrowFunctor`: the covariant functor
  `M ↦ J(M)`, the natural transformation `𝟭 ⟶ jModuleFunctor` given by the canonical maps, and
  the resulting functor into the arrow category.

## Main results

* `characterModule_finsupp_injective`: the character module of a free module is injective.
* `jModule_injective`: `J(M)` is injective.
* `moduleCat_hasFunctorialInjectiveEmbeddings`: `jModuleArrowFunctor` exhibits functorial
  injective embeddings for `R`-modules.
* `moduleCat_hasFunctorialInjectiveEmbeddings'`: the category of `R`-modules has functorial
  injective embeddings.

## Implementation notes

Following the Stacks Project's convention that "ring" means commutative unital ring, `R` is a
`CommRing`; commutativity is what makes `(r • φ)(x) = φ(r • x)` a left module structure on `M^∨`.
Mathlib's `Module.Injective R J` is the lifting property along injective linear maps, its
`CharacterModule` is `M^∨` with `ℚ/ℤ` modelled as `AddCircle (1 : ℚ)`, and the free `R`-module on
the underlying set of `N` is `N →₀ R`, whose canonical basis is indexed by the elements of `N`.

`JModule` needs no `Module R M`: the inner character module enters only as an index type, and the
outer one is an `R`-module because `M^∨ →₀ R` is. The canonical map `M → J(M)` does use the module
structure on `M`, and so is stated separately.

## References

* [Stacks Project, Tag 01D9](https://stacks.math.columbia.edu/tag/01D9)
* [Stacks Project, Tag 01DC](https://stacks.math.columbia.edu/tag/01DC)
* [Stacks Project, Tag 01DD](https://stacks.math.columbia.edu/tag/01DD)
-/

@[expose] public section

open CategoryTheory

universe u v

/-! ### The free module on the underlying set of a module -/

/-- The natural surjection `F(M) → M`, `Σ f_i [m_i] ↦ Σ f_i m_i`, where the free `R`-module
`F(M) = ⨁_{m ∈ M} R[m]` is modelled as `M →₀ R`. -/
noncomputable def freeSurj (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    (M →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R id

/-- `freeSurj` sends `Σ f_i [m_i]` to `Σ f_i • m_i`. -/
theorem freeSurj_apply {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (f : M →₀ R) : freeSurj R M f = f.sum (fun m r => r • m) := by
  simp [freeSurj, Finsupp.linearCombination, Finsupp.lsum]

/-- The natural map `F(M) → M` is surjective. -/
theorem freeSurj_surjective (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Surjective (freeSurj R M) :=
  Finsupp.linearCombination_id_surjective R M

/-- The covers `F(M) → M` are natural in `M`: re-indexing a free-module element along a linear
map `g` and then summing agrees with summing and then applying `g`. -/
theorem freeSurj_comp_lmapDomain {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) :
    (freeSurj R N).comp (Finsupp.lmapDomain R R (g : M → N)) = g.comp (freeSurj R M) := by
  ext p
  simp [freeSurj]

/-- The functor sending an `R`-module `M` to the natural epimorphism `F(M) → M`, where `F(M)` is
the free module on the underlying set of `M`. Landing in the full subcategory of the arrow
category spanned by the epimorphisms retains the surjectivity of each cover. -/
@[stacks 01D9 "the free module on the underlying set of a module, with its natural surjection"]
noncomputable def freeModuleCoverFunctor (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ (MorphismProperty.epimorphisms (ModuleCat.{u} R)).Arrow ⊤ ⊤ where
  obj M := MorphismProperty.Arrow.mk ((ModuleCat.adj R).counit.app M) (by
    rw [MorphismProperty.epimorphisms, ModuleCat.epi_iff_surjective]
    intro m
    refine ⟨ModuleCat.freeMk m, ?_⟩
    simp [ModuleCat.adj, ModuleCat.freeHomEquiv])
  map f := MorphismProperty.Arrow.homMk
      ((ModuleCat.free R).map ((forget (ModuleCat.{u} R)).map f)) f
      ((ModuleCat.adj R).counit.naturality f)
  map_id M := by
    apply MorphismProperty.Arrow.Hom.ext
    · change (ModuleCat.free R).map ((forget (ModuleCat.{u} R)).map (𝟙 M)) = 𝟙 _
      rw [(forget (ModuleCat.{u} R)).map_id, (ModuleCat.free R).map_id]
    · rfl
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change (ModuleCat.free R).map ((forget (ModuleCat.{u} R)).map (f ≫ g)) =
        (ModuleCat.free R).map ((forget (ModuleCat.{u} R)).map f) ≫
          (ModuleCat.free R).map ((forget (ModuleCat.{u} R)).map g)
      rw [(forget (ModuleCat.{u} R)).map_comp, (ModuleCat.free R).map_comp]
    · rfl

/-! ### The injective module `J(M)` -/

/-- `J(M) = (F(M^∨))^∨`. -/
abbrev JModule (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] : Type _ :=
  CharacterModule (CharacterModule M →₀ R)

/-- **Stacks Tag 01DC, Lemma 15.56.8.**
For every `R`-module `M` (with `R` commutative), the `R`-module `J(M) = (F(M^∨))^∨` is
injective. This is `characterModule_finsupp_injective` for the index type `M^∨`. -/
@[stacks 01DC]
theorem jModule_injective (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] :
    Module.Injective R (JModule R M) :=
  Module.Flat.iff_characterModule_injective.mp inferInstance

/-! ### Functorial injective embeddings -/

section Functorial

variable (R : Type u) [CommRing R]

/-- The canonical map `M → J(M) = (F(M^∨))^∨`: evaluate `M` into `(M^∨)^∨`, then dualise the
cover `F(M^∨) → M^∨`. -/
noncomputable def jModuleEmbedding (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] JModule R M :=
  (CharacterModule.dual (freeSurj R (CharacterModule M))).comp (CharacterModule.evalₗ R M)

/-- The canonical map `M → J(M)` sends `x` to the character on `F(M^∨)` that evaluates at `x`
the image in `M^∨` of a free-module element. -/
@[simp]
theorem jModuleEmbedding_apply {M : Type v} [AddCommGroup M] [Module R M]
    (x : M) (p : CharacterModule M →₀ R) :
    jModuleEmbedding R M x p = freeSurj R (CharacterModule M) p x :=
  rfl

/-- The canonical map `M → J(M)` is injective: evaluation is injective, and dualising a
surjection gives an injection. -/
theorem jModuleEmbedding_injective (M : Type v) [AddCommGroup M] [Module R M] :
    Function.Injective (jModuleEmbedding R M) :=
  (CharacterModule.dual_injective_of_surjective _
      (freeSurj_surjective R (CharacterModule M))).comp
    (CharacterModule.evalₗ_injective R M)

/-- The contravariant action of `M ↦ F(M^∨)` on a linear map: re-index the free module along
the dual map. -/
noncomputable def freeDualMap {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (CharacterModule N →₀ R) →ₗ[R] (CharacterModule M →₀ R) :=
  Finsupp.lmapDomain R R (CharacterModule.dual (R := R) f)

/-- `freeDualMap` sends the identity to the identity. -/
@[simp]
theorem freeDualMap_id (M : Type v) [AddCommGroup M] [Module R M] :
    freeDualMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  rw [freeDualMap, CharacterModule.dual_id, LinearMap.id_coe, Finsupp.lmapDomain_id]

/-- `freeDualMap` reverses composition. -/
theorem freeDualMap_comp {M N P : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    freeDualMap R (g.comp f) = (freeDualMap R f).comp (freeDualMap R g) := by
  rw [freeDualMap, freeDualMap, freeDualMap, CharacterModule.dual_comp,
    LinearMap.coe_comp, Finsupp.lmapDomain_comp]

/-- The covariant action of `M ↦ J(M)` on a linear map: apply character duality, the
free-module construction, and character duality once more. -/
noncomputable def jModuleMap {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : JModule R M →ₗ[R] JModule R N :=
  CharacterModule.dual (freeDualMap R f)

/-- `jModuleMap` sends the identity to the identity. -/
@[simp]
theorem jModuleMap_id (M : Type v) [AddCommGroup M] [Module R M] :
    jModuleMap R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  rw [jModuleMap, freeDualMap_id, CharacterModule.dual_id]

/-- `jModuleMap` preserves composition. -/
theorem jModuleMap_comp {M N P : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    jModuleMap R (g.comp f) = (jModuleMap R g).comp (jModuleMap R f) := by
  rw [jModuleMap, jModuleMap, jModuleMap, freeDualMap_comp, CharacterModule.dual_comp]

/-- The covariant functor `M ↦ J(M) = (F(M^∨))^∨`. -/
noncomputable def jModuleFunctor : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (JModule R M)
  map f := ModuleCat.ofHom (jModuleMap R f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    change jModuleMap R (ModuleCat.Hom.hom (𝟙 M)) = LinearMap.id
    rw [ModuleCat.hom_id, jModuleMap_id]
  map_comp f g := by
    apply ModuleCat.hom_ext
    change jModuleMap R (ModuleCat.Hom.hom (f ≫ g)) =
      (jModuleMap R g.hom).comp (jModuleMap R f.hom)
    rw [ModuleCat.hom_comp, jModuleMap_comp]

/-- The canonical maps `M → J(M)` form a natural transformation from the identity functor to
`jModuleFunctor`: the square commutes because evaluation and the free-module covers are both
natural, and character duality is a functor. -/
noncomputable def jModuleEmbeddingNatTrans :
    Functor.id (ModuleCat.{max u v} R) ⟶ jModuleFunctor R where
  app M := ModuleCat.ofHom (jModuleEmbedding R M)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    change (jModuleEmbedding R N).comp f.hom = (jModuleMap R f.hom).comp (jModuleEmbedding R M)
    rw [jModuleEmbedding, jModuleEmbedding, jModuleMap, freeDualMap, LinearMap.comp_assoc,
      CharacterModule.evalₗ_naturality f.hom, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
      ← CharacterModule.dual_comp, ← CharacterModule.dual_comp,
      freeSurj_comp_lmapDomain (CharacterModule.dual (R := R) f.hom)]

/-- The canonical arrow-valued functor `M ↦ (M → J(M))`. Its action on morphisms is the
naturality square for the evaluation/free-cover/dual construction. -/
noncomputable def jModuleArrowFunctor :
    ModuleCat.{max u v} R ⥤ Arrow (ModuleCat.{max u v} R) where
  obj M := Arrow.mk ((jModuleEmbeddingNatTrans R).app M)
  map f := Arrow.homMk' f ((jModuleFunctor R).map f) ((jModuleEmbeddingNatTrans R).naturality f)
  map_id M := Arrow.hom_ext _ _ rfl ((jModuleFunctor R).map_id M)
  map_comp f g := Arrow.hom_ext _ _ rfl ((jModuleFunctor R).map_comp f g)

/-- **Stacks Project, Tag 01DD.** The canonical maps `M → J(M) = (F(M^∨))^∨` form a covariant
functor from `R`-modules to arrows of `R`-modules whose source projection is the identity, each
of whose components is a monomorphism, and each of whose targets is an injective module. -/
@[stacks 01DD]
theorem moduleCat_hasFunctorialInjectiveEmbeddings :
    IsFunctorialInjectiveEmbeddings₁ (ModuleCat.{max u v} R) (jModuleArrowFunctor R) ∧
      IsFunctorialInjectiveEmbeddings₂ (ModuleCat.{max u v} R) (jModuleArrowFunctor R) ∧
        IsFunctorialInjectiveEmbeddings₃ (ModuleCat.{max u v} R) (jModuleArrowFunctor R) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro M
    show Mono (ModuleCat.ofHom (jModuleEmbedding R M))
    rw [ModuleCat.mono_iff_injective]
    exact jModuleEmbedding_injective R M
  · intro M
    exact (Module.injective_iff_injective_object R _).mp (jModule_injective R M)

/-- The category of `R`-modules has functorial injective embeddings in the sense of Stacks
Tag 0139, witnessed by `jModuleArrowFunctor`. -/
theorem moduleCat_hasFunctorialInjectiveEmbeddings' :
    HasFunctorialInjectiveEmbeddings (ModuleCat.{max u v} R) :=
  ⟨jModuleArrowFunctor R, moduleCat_hasFunctorialInjectiveEmbeddings R⟩

end Functorial

end
