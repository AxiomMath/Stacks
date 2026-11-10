module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial

/-!
# The conormal module of a closed subspace in its first order neighbourhood

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S` contained in a big fppf
site `B`, with defining ideal sheaf `𝓘 ⊆ 𝒪_X`, and let `Z'` be its first order infinitesimal
neighbourhood: the closed subspace of `X` with defining ideal sheaf `𝓘²`
(`AlgebraicGeometry.Space.IsFirstOrderNeighbourhood`).  This file proves that the map of
conormal modules `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP] attached to the square
```
Z --→ Z'
|     |
Z --→ X
```
is an isomorphism.  This is [Stacks Project, Tag 05ZX] for a closed immersion; the immersion case
is `AlgebraicGeometry.Space.isIso_immersionLiftConormalMap` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderNeighbourhoodImmersion.lean`, which
reduces to the result here.

The base's `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleFirstOrderNeighbourhoodIso.lean`
proves the same isomorphism, `AlgebraicGeometry.Space.isIso_conormalMap_of_ker_eq_ker_sq`, from
the chartwise description of the neighbourhood (the kernel on every étale chart is the square of
that of `Z`); the form here takes the neighbourhood as
`AlgebraicGeometry.Space.IsFirstOrderNeighbourhood`, equality of defining ideal sheaves.

## Main results

* `CategoryTheory.Adjunction.isIso_map_of_comp_homEquiv_eq_zero`: an abstract criterion for the
  image `F'(ψ)` of an epimorphism `ψ : F A ⟶ B` under a left adjoint to be an isomorphism, in
  terms of the transposes along a second adjunction `F ⊣ G` with `G` faithful.
* `Stacks.IdealPowerSheaf.apply_eq_zero_of_mem_idealPow_two`: a morphism out of a sheaf of
  ideals `𝓘` into a module annihilated by `𝓘` kills the sections of `𝓘` lying in `𝓘²`.
* `AlgebraicGeometry.Space.isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood`:
  the inverse image along `Z ⟶ Z'` of the map `j^*𝓘 ⟶ 𝓘_{Z/Z'}` of defining ideal sheaves is an
  isomorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_firstOrderNeighbourhood`: **the map
  `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP] is an isomorphism.**

## The proof

Write `j : Z' ⟶ X` and `i' : Z ⟶ Z'` for the inclusions, `𝓙 ⊆ 𝒪_{Z'}` for the defining ideal of
`Z` in `Z'`, and `ψ : j^*𝓘 ⟶ 𝓙` for the map of defining ideal sheaves.  The conormal map is an
isomorphism followed by `i'^*ψ`, and `i'^*ψ` is invertible as soon as every morphism
`θ : j^*𝓘 ⟶ i'_*N` factors through the epimorphism `ψ` (Yoneda).  That is the statement that `θ`
kills the kernel of `ψ`; transposing along `j^* ⊣ j_*`, whose right adjoint is faithful because
`j` is a closed immersion, and using that the unit `𝓘 ⟶ j_*j^*𝓘` is an epimorphism, it becomes:
every section of `𝓘` killed by the transpose `𝓘 ⟶ j_*𝓙` of `ψ` is killed by the transpose
`𝓘 ⟶ j_*i'_*N` of `θ`.  A section of `𝓘` killed by the transpose of `ψ` vanishes on `Z'`, so it
is a section of the defining ideal `𝓘²` of `Z'`; and `j_*i'_*N` is a direct image along the
inclusion of `Z`, so it is annihilated by `𝓘` and the transpose of `θ` kills `𝓘²`.

This is the source's argument — under the quotient description `i_*𝒞_{Z/X} = 𝓘/𝓘²` of
[Stacks Project, Tag 04CN] both sides are `𝓘/𝓘²` — run through the universal properties, so that
no description of the sections of an inverse image is needed.

## References

* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

/-- **An invertibility criterion for the image of an epimorphism under a left adjoint.**  Let
`F ⊣ G` be an adjunction between abelian categories with `G` faithful, let `A` be an object whose
unit `A ⟶ G F A` is an epimorphism, and let `ψ : F A ⟶ B` be an epimorphism.  Let `F' ⊣ G'` be a
second adjunction out of the target category.  If every morphism `k : P ⟶ A` killed by the
transpose of `ψ` is killed by the transpose of every `θ : F A ⟶ G' N`, then `F' ψ` is an
isomorphism.

Indeed `F' ψ` is invertible when precomposition with `ψ` is a bijection onto the morphisms into
every `G' N`; it is injective because `ψ` is an epimorphism, and surjective when every such `θ`
kills the kernel of `ψ`, which is checked after applying the faithful `G` and pulling back along
the epimorphic unit. -/
theorem isIso_map_of_comp_homEquiv_eq_zero {C D E : Type*} [Category C] [Category D]
    [Category E] [Abelian C] [Abelian D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Faithful]
    {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
    {A : C} {B : D} (ψ : F.obj A ⟶ B) [Epi ψ] [Epi (adj.unit.app A)]
    (h : ∀ (N : E) (θ : F.obj A ⟶ G'.obj N) {P : C} (k : P ⟶ A),
      k ≫ adj.homEquiv _ _ ψ = 0 → k ≫ adj.homEquiv _ _ θ = 0) :
    IsIso (F'.map ψ) := by
  have := adj.isRightAdjoint
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isRightAdjoint G
  refine isIso_of_coyoneda_map_bijective _ fun N => ?_
  have key : Function.Bijective fun σ : B ⟶ G'.obj N => ψ ≫ σ := by
    refine ⟨fun σ₁ σ₂ e => (cancel_epi ψ).1 e, fun θ => ?_⟩
    have hz : kernel.ι ψ ≫ θ = 0 := by
      refine G.map_injective ?_
      rw [G.map_comp, G.map_zero]
      have hsnd : Epi (pullback.snd (adj.unit.app A) (G.map (kernel.ι ψ))) :=
        Abelian.epi_pullback_of_epi_f _ _
      refine (cancel_epi (pullback.snd (adj.unit.app A) (G.map (kernel.ι ψ)))).1 ?_
      rw [comp_zero, ← Category.assoc, ← pullback.condition, Category.assoc]
      have hk := h N θ (pullback.fst (adj.unit.app A) (G.map (kernel.ι ψ))) (by
        rw [adj.homEquiv_unit, ← Category.assoc, pullback.condition, Category.assoc,
          ← G.map_comp, kernel.condition, G.map_zero, comp_zero])
      rwa [adj.homEquiv_unit] at hk
    exact ⟨Abelian.epiDesc ψ θ hz, Abelian.comp_epiDesc ψ θ hz⟩
  have hcomm : ∀ x : F'.obj B ⟶ N,
      adj'.homEquiv _ _ (F'.map ψ ≫ x) = ψ ≫ adj'.homEquiv _ _ x :=
    fun x => adj'.homEquiv_naturality_left ψ x
  refine ⟨fun x y hxy => (adj'.homEquiv _ _).injective (key.1 ?_), fun θ => ?_⟩
  · simp only at hxy ⊢
    rw [← hcomm, ← hcomm, hxy]
  · obtain ⟨σ, hσ⟩ := key.2 (adj'.homEquiv _ _ θ)
    refine ⟨(adj'.homEquiv _ _).symm σ, (adj'.homEquiv _ _).injective ?_⟩
    simp only
    rwa [hcomm, Equiv.apply_symm_apply]

end CategoryTheory.Adjunction

namespace Stacks.IdealPowerSheaf

section Image

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{u} R}

/-- The image in `M` of a submodule `K` of a submodule `N ⊆ M`: the sections of `N` lying in
`K`, read as sections of `M`. -/
private noncomputable def submoduleImage (N : M.Submodule) (K : N.toSheafOfModules.Submodule) :
    M.Submodule where
  obj V := (K.obj V).map (N.obj V).subtype
  map {V V'} f y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N.toPresheafOfModules.map f x, K.map f hx, rfl⟩
  isSheaf {V} y hy := by
    have hyN : y ∈ N.obj V := by
      refine N.isSheaf y (J.superset_covering (fun W g hg => ?_) hy)
      obtain ⟨x, -, hx⟩ := hg
      change M.val.map g.op y ∈ N.obj (op W)
      have hx' : (x : M.val.obj (op W)) = M.val.map g.op y := hx
      exact hx' ▸ x.2
    refine ⟨⟨y, hyN⟩, K.isSheaf _ (J.superset_covering (fun W g hg => ?_) hy), rfl⟩
    obtain ⟨x, hx, hxy⟩ := hg
    have : (N.toSheafOfModules.val.map g.op ⟨y, hyN⟩ : N.toSheafOfModules.val.obj (op W)) = x :=
      Subtype.ext hxy.symm
    change N.toSheafOfModules.val.map g.op ⟨y, hyN⟩ ∈ K.obj (op W)
    rwa [this]

/-- A section of `N` lies in the image of `K` exactly when it lies in `K`. -/
private theorem mem_submoduleImage_iff (N : M.Submodule) (K : N.toSheafOfModules.Submodule)
    {V : Cᵒᵖ} (x : N.toSheafOfModules.val.obj V) :
    (x.1 : M.val.obj V) ∈ (submoduleImage N K).obj V ↔ x ∈ K.obj V := by
  constructor
  · rintro ⟨x', hx', hxx⟩
    rwa [← (Subtype.ext hxx : x' = x)]
  · exact fun hx => ⟨x, hx, rfl⟩

/-- **A morphism out of a sheaf of ideals into a module it annihilates kills the square of the
ideal.**  Let `I ⊆ R` be a sheaf of ideals and `θ : I ⟶ M` a morphism of sheaves of modules
into a module annihilated by `I`.  Every section of `I` lying in `I²` is killed by `θ`: a
product `a · m` of sections of `I` is sent to `a · θ(m) = 0`, and the sections killed by `θ` form
a sheaf submodule. -/
theorem apply_eq_zero_of_mem_idealPow_two (I : (SheafOfModules.unit R).Submodule)
    (θ : I.toSheafOfModules ⟶ M)
    (hann : ∀ (V : Cᵒᵖ) (a : R.obj.obj V), a ∈ I.obj V → ∀ m : M.val.obj V, a • m = 0)
    {V : Cᵒᵖ} (x : I.toSheafOfModules.val.obj V)
    (hx : (x.1 : (SheafOfModules.unit R).val.obj V) ∈ (idealPow I 2).obj V) :
    θ.val.app V x = 0 := by
  have hle : idealPow I 2 ≤ submoduleImage I (SheafOfModules.Submodule.ker θ) := by
    refine sInf_le fun U a ha m hm => ?_
    replace hm : m ∈ I.obj U := hm
    have hm' : a • m ∈ I.obj U := (I.obj U).smul_mem a hm
    refine (mem_submoduleImage_iff I _ (⟨a • m, hm'⟩ : I.toSheafOfModules.val.obj U)).2 ?_
    have hsm : (⟨a • m, hm'⟩ : I.toSheafOfModules.val.obj U) =
        a • (⟨m, hm⟩ : I.toSheafOfModules.val.obj U) := rfl
    change θ.val.app U ⟨a • m, hm'⟩ = 0
    rw [hsm]
    exact ((θ.val.app U).hom.map_smul a _).trans (hann U a ha _)
  exact (mem_submoduleImage_iff I _ x).1 (hle V hx)

end Image

end Stacks.IdealPowerSheaf

namespace AlgebraicGeometry.Space

open Stacks.IdealPowerSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Neighbourhood

variable (X : AlgebraicSpaces B S hS) (Z Z' : ClosedSubspaces B S hS X.1)

/-- The transpose `𝓘_Z ⟶ j_*𝓘_{Z/Z'}` of the map of defining ideal sheaves of the square of a pair
of closed subspaces `Z, Z' ⊆ X`, along the inclusion `j : Z' ⟶ X`, kills only sections lying in
the defining ideal of `Z'`: followed by the inclusion `j_*𝓘_{Z/Z'} ⊆ j_*𝒪_{Z'}` it is the
inclusion `𝓘_Z ⊆ 𝒪_X` followed by the structure map `j^♯`, whose kernel is the defining ideal of
`Z'`. -/
private theorem mem_definingIdealAt_of_homEquiv_idealSheafMap_eq_zero
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj V)
    (hx : ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z')).homEquiv _ _
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
        (subspaceInclusion B S hS X Z')
        (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z))).val.app V x
        = 0) :
    (x.1 : (structureRingSheaf B S hS X).obj.obj V) ∈ definingIdealAt B S hS X Z' V := by
  have E := idealSheafMap_comp_definingIdealSheaf_ι B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
    (subspaceInclusion B S hS X Z')
    (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)
  have E' := congrArg ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z')).homEquiv
    _ _) E
  have E'' := ((modulePullbackAdjunction B S hS
      (subspaceInclusion B S hS X Z')).homEquiv_naturality_right _ _).symm.trans (E'.trans
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z')).homEquiv_naturality_left
      _ _))
  have hsec := congrArg (fun m => m.val.app V x) E''
  have hT := congrArg (fun m => m.hom.app V x.1)
    (moduleSheafFunctor_map_homEquiv_structureModulePullbackMap B S hS
      (subspaceInclusion B S hS X Z'))
  simp only at hsec hT
  refine (mem_definingIdealAt_iff B S hS X Z' V x.1).2 ?_
  refine Eq.trans hT.symm (Eq.trans hsec.symm ?_)
  exact (congrArg (fun y => ((modulePushforward B S hS (subspaceInclusion B S hS X Z')).map
    (definingIdealSheaf B S hS _
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z)).ι).val.app V y) hx).trans
    (map_zero _)

/-- A direct image along the inclusion `Z' ⟶ X` of a direct image along the inclusion of the
inverse image of `Z` in `Z'` is annihilated by the defining ideal of `Z`. -/
private theorem smul_eq_zero_modulePushforward_preimage
    (N : Modules.{u, u} B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z).1.toFunctor
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z).2.1)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (a : (structureRingSheaf B S hS X).obj.obj V)
    (ha : a ∈ definingIdealAt B S hS X Z V) :
    letI M := (modulePushforward B S hS (subspaceInclusion B S hS X Z')).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))).obj N)
    letI : Module ((structureRingSheaf B S hS X).obj.obj V) (M.val.obj V) := (M.val.obj V).isModule
    ∀ m : M.val.obj V, a • m = 0 := by
  have hann := annihilatedByKerIdeal_of_essImage_modulePushforward B S hS
    (subspaceInclusion B S hS _
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) ≫
        subspaceInclusion B S hS X Z')
    ⟨N, ⟨((modulePushforwardCompIso B S hS
          (subspaceInclusion B S hS _
            (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))
          (subspaceInclusion B S hS X Z')).app N).symm⟩⟩
  refine hann V a ((SheafOfModules.mem_kerIdeal _ V a).2 ?_)
  exact kernelIdealSheaf_le_comp B S hS _ (subspaceInclusion B S hS X Z)
    (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
    (subspaceInclusion B S hS X Z')
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z) V ha

/-- **The inverse image along `Z ⟶ Z'` of the map of defining ideal sheaves is invertible.**
Let `Z'` be the first order infinitesimal neighbourhood of a closed subspace `Z` of `X`, with
inclusion `j : Z' ⟶ X`.  The inverse image along the inclusion of `Z` into `Z'` of the map
`j^*𝓘_Z ⟶ 𝓘_{Z/Z'}` of [Stacks Project, Tag 04CP] is an isomorphism.

This is `CategoryTheory.Adjunction.isIso_map_of_comp_homEquiv_eq_zero` for `j^* ⊣ j_*`: the
direct image along the closed immersion `j` is faithful, the unit at `𝓘_Z` is an epimorphism,
the map of ideal sheaves is an epimorphism by the surjectivity clause of
[Stacks Project, Tag 04CQ], and a section of `𝓘_Z` killed by its transpose lies in the defining
ideal `𝓘_Z²` of `Z'`, which every morphism into a module annihilated by `𝓘_Z` kills. -/
theorem isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood
    (h : IsFirstOrderNeighbourhood B S hS X Z Z') :
    IsIso ((modulePullback B S hS (subspaceInclusion B S hS _
        (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))).map
      (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
        (subspaceInclusion B S hS X Z')
        (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z))) := by
  have hj : IsClosedImmersion B S hS (subspaceInclusion B S hS X Z').hom := Z'.2.2
  have := (fullyFaithfulModulePushforward B S hS _ hj).faithful
  have := epi_idealSheafMap B S hS (subspaceInclusion B S hS X Z') Z
  have := epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS _ hj
    (fun M hM => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS _ hj M hM)
    (definingIdealSheaf B S hS X Z).toSheafOfModules
  refine Adjunction.isIso_map_of_comp_homEquiv_eq_zero (modulePullbackAdjunction B S hS _)
    (modulePullbackAdjunction B S hS _) _ ?_
  intro N θ P k hk
  ext V x
  have hy := congrArg (fun m => m.val.app V x) hk
  have h2 : ((k.val.app V x).1 : (structureRingSheaf B S hS X).obj.obj V) ∈
      (idealPow (definingIdealSheaf B S hS X Z) 2).obj V := by
    rw [← h]
    exact mem_definingIdealAt_of_homEquiv_idealSheafMap_eq_zero B S hS X Z Z' V
      (k.val.app V x) (hy.trans rfl)
  exact (apply_eq_zero_of_mem_idealPow_two (definingIdealSheaf B S hS X Z)
    ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z')).homEquiv _ _ θ)
    (fun V a ha m => smul_eq_zero_modulePushforward_preimage B S hS X Z Z' N V a ha m)
    (k.val.app V x) h2).trans rfl

/-- **[Stacks Project, Tag 05ZX] for a closed immersion.**  Let `Z` be a closed subspace of an
algebraic space `X` and let `Z'` be its first order infinitesimal neighbourhood, the closed
subspace whose defining ideal sheaf is the square of that of `Z`.  The map of conormal modules
`𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04CP] induced by the square with `Z` on both sides
is an isomorphism.

As in `AlgebraicGeometry.Space.epi_conormalMap_firstOrderNeighbourhood`, `Z` is read as a closed
subspace of `Z'` through the inverse image along `Z' ⟶ X`, and the left vertical morphism is the
projection of that inverse image onto `Z`.  The conormal map is the comparison isomorphism
followed by the inverse image of the map of defining ideal sheaves, which is invertible by
`AlgebraicGeometry.Space.isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood`.
The statement for an immersion is
`AlgebraicGeometry.Space.isIso_immersionLiftConormalMap`. -/
theorem isIso_conormalMap_firstOrderNeighbourhood
    (h : IsFirstOrderNeighbourhood B S hS X Z Z') :
    IsIso (conormalMap B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
      (subspaceInclusion B S hS X Z')
      (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)) := by
  have hc := isIso_conormalPullbackComparison B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
    (subspaceInclusion B S hS X Z')
    (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)
  have hp : @IsIso _ _
      ((modulePullback B S hS (subspaceInclusion B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))).obj
        ((modulePullback B S hS (subspaceInclusion B S hS X Z')).obj
          (definingIdealSheaf B S hS X Z).toSheafOfModules))
      (conormalModule B S hS _ (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))
      ((modulePullback B S hS (subspaceInclusion B S hS _
          (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z))).map
        (idealSheafMap B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
          (subspaceInclusion B S hS X Z')
          (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
          (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z))) :=
    isIso_modulePullback_map_idealSheafMap_of_isFirstOrderNeighbourhood B S hS X Z Z' h
  rw [conormalMap_eq B S hS (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
    (subspaceInclusion B S hS X Z')
    (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)]
  exact IsIso.comp_isIso

end Neighbourhood

end AlgebraicGeometry.Space
