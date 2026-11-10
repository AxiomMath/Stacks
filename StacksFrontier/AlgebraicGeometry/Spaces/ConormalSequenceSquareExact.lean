module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFactorizationVanishing

/-!
# Exactness in the middle of the conormal sequence of a square

Let `h : M ⟶ N` be a morphism of algebraic spaces over `S`, let `Y ⊆ N` and `Z ⊆ M` be closed
subspaces, and let `f : Z ⟶ Y` make the square `Z ⟶ M ⟶ N = Z ⟶ Y ⟶ N` commute.  Write
`P = h⁻¹(Y) = Y ×_N M`, with inclusion `j : P ⟶ M`, and `W = j⁻¹(Z)` for the copy of `Z` inside
`P`, with projection `π : W ⟶ Z`.  The maps of Stacks 04CP form a sequence

`π^*f^*𝒞_{Y/N} ⟶ π^*𝒞_{Z/M} ⟶ 𝒞_{W/P} ⟶ 0`

and `AlgebraicGeometry.Space.exact_conormalMap_square` proves it **exact in the middle**, with no
hypothesis on the square.  (The epimorphism at the right is the surjectivity clause of
Stacks 04CQ, `AlgebraicGeometry.Space.epi_conormalMap`.)  This is the mathematical content of the
exactness in clause (2) of Stacks 06BF, which is its instance at the square of two universal
first-order thickenings
(`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningCompositionExact.lean`),
and with `h` the identity it is the exactness in the middle of the conormal sequence of a pair of
closed subspaces `Z ⊆ Y ⊆ X`, the middle clause of Stacks 06BD at the level of algebraic spaces.

## The proof

No chart is used.  Everything is a statement about the defining ideal sheaves and the structure
maps on the small étale sites, in four steps.

1. **On `M`** (`AlgebraicGeometry.Space.exact_and_epi_squareIdealTranspose`): the sequence
   `𝓘_P ⟶ 𝓘_Z ⟶ j_*𝓘_W ⟶ 0` is exact.  `𝓘_Z` is the kernel of the composite projection
   `𝒪_M ⟶ j_*𝒪_P ⟶ j_*ι_*𝒪_W`, by the composition law of the structure maps of Stacks 03G8
   (`AlgebraicGeometry.Space.structureSharpSet_comp`) and the factorization of `Z ⟶ M` through
   `W` (`AlgebraicGeometry.Space.kernelIdealSheaf_squareSub_comp`); `𝓘_P` is the kernel of the
   first projection, which is an epimorphism by Stacks 03MB; `j_*𝓘_W` is the kernel of the direct
   image of the second, `j_*` being a right adjoint; and the abstract lemma
   `CategoryTheory.Abelian.exact_and_epi_of_kernel_comp` concludes.  The map `𝓘_Z ⟶ j_*𝓘_W` is
   identified with the transpose of `AlgebraicGeometry.Space.idealSheafMap` on chart diagrams
   (`AlgebraicGeometry.Space.squareIdealTranspose_comp_ι`).
2. **Still on `M`** (`AlgebraicGeometry.Space.exact_idealSheafMap_squareIdealTranspose`): the map
   `h^*𝓘_Y ⟶ 𝓘_Z` of Stacks 04CP factors through the epimorphism `h^*𝓘_Y ⟶ 𝓘_P` of the fibre
   product square (Stacks 04CQ, `AlgebraicGeometry.Space.epi_idealSheafMap`), so
   `h^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_W ⟶ 0` is exact.
3. **On `P` and on `W`**: the inverse image along `j` is right exact, and the counit
   `j^*j_*𝓘_W ⟶ 𝓘_W` is an isomorphism because `j` is a closed immersion (Stacks 04CJ, part (2)),
   so `j^*h^*𝓘_Y ⟶ j^*𝓘_Z ⟶ 𝓘_W ⟶ 0` is exact; the inverse image along `ι_W` is right exact.
4. **Comparison**: the conormal sequence is isomorphic to the last one, by the comparison
   isomorphisms `AlgebraicGeometry.Space.conormalPullbackCompIso` and their naturality
   (`AlgebraicGeometry.Space.conormalMap_comp_conormalPullbackComparison`).

## Implementation notes

Two spellings of the same categories meet here, `AlgebraicGeometry.Space.Modules` and
`SheafOfModules (structureRingSheaf X)`, and with them two failure modes, both worked around
rather than fought.

* Instance search for the abelian structure of `Modules` in this import closure tries Mathlib's
  `SheafOfModules` instance at an unsolved module universe and stops on a universe constraint.
  The private local instance `modulesAbelian`, Mathlib's instance with its two hypotheses
  supplied at the universe `u`, is in scope for the ideal-level section only, and statements
  there name the category `Modules.{u, u}` explicitly where a zero morphism or an epimorphism is
  formed.  The two lemmas `CategoryTheory.ShortComplex.exact_mk_congr_hasZeroMorphisms` and
  `CategoryTheory.Limits.comp_eq_zero_congr_hasZeroMorphisms` move statements between the zero
  morphisms of that section and those found elsewhere.
* Unfolding `AlgebraicGeometry.Space.modulePullback` does not terminate in practice, so, as in
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleComposition.lean`, it is locally
  irreducible in the sections that compare conormal maps.  The abbreviation for `π` carries its
  type: inferred, its type spells the source differently from the other abbreviations and the
  comparison of the two spellings exhausts the budget.

## References

* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Abelian C]

/-- **The kernel of a composite onto the kernel of the second map.**  In an abelian category let
`p : O ⟶ A` be an epimorphism and `c : A ⟶ C₃` a morphism, let `k : K ⟶ O` be a monomorphism
through which every morphism killed by `p ≫ c` factors, let `m : Kc ⟶ A` be a monomorphism killed
by `c`, and let `ι : Kp ⟶ O` be a morphism through which every morphism killed by `p` factors.
Let `l : Kp ⟶ K` and `φ : K ⟶ Kc` be monomorphism and morphism with `l ≫ k = ι` and
`φ ≫ m = k ≫ p`.  Then `Kp ⟶ K ⟶ Kc` is exact and `φ` is an epimorphism.

In the application `O` is a structure sheaf, `p` and `c` are two successive projections onto
direct images of structure sheaves, `K` is the defining ideal of the composite and `Kp` the
defining ideal of the first. -/
theorem exact_and_epi_of_kernel_comp {O A C₃ K Kc Kp : C} (p : O ⟶ A) [Epi p] (c : A ⟶ C₃)
    (k : K ⟶ O) [Mono k] (hk : ∀ {T : C} (x : T ⟶ O), x ≫ p ≫ c = 0 → ∃ y, y ≫ k = x)
    (m : Kc ⟶ A) [Mono m] (hmc : m ≫ c = 0)
    (ι : Kp ⟶ O) (hι : ∀ {T : C} (x : T ⟶ O), x ≫ p = 0 → ∃ y, y ≫ ι = x)
    (l : Kp ⟶ K) [Mono l] (hl : l ≫ k = ι) (φ : K ⟶ Kc) (hφ : φ ≫ m = k ≫ p)
    (w : l ≫ φ = 0) :
    (ShortComplex.mk l φ w).Exact ∧ Epi φ := by
  refine ⟨ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {T} x hx => ?_),
    ?_⟩
  · have hx' : (x ≫ k) ≫ p = 0 := by
      rw [Category.assoc, ← hφ, ← Category.assoc, hx, zero_comp]
    refine ⟨(hι _ hx').choose, ?_⟩
    rw [← cancel_mono k, Category.assoc, hl]
    exact (hι _ hx').choose_spec
  · have hfst : pullback.fst p m ≫ p ≫ c = 0 := by
      rw [← Category.assoc, pullback.condition, Category.assoc, hmc, comp_zero]
    obtain ⟨y, hy⟩ := hk _ hfst
    have hyφ : y ≫ φ = pullback.snd p m := by
      rw [← cancel_mono m, Category.assoc, hφ, ← Category.assoc, hy, pullback.condition]
    exact epi_of_epi_fac hyφ

end CategoryTheory.Abelian

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A short complex related to an exact one by isomorphisms of its three terms commuting with the
two arrows is exact.  The arrows are explicit arguments, so the two short complexes are formed
at exactly the given morphisms. -/
theorem exact_of_isIso_comm {A₁ A₂ A₃ B₁ B₂ : C} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃)
    (w : f ≫ g = 0) (f' : B₁ ⟶ B₂) (g' : B₂ ⟶ A₃) (w' : f' ≫ g' = 0)
    (e₁ : A₁ ⟶ B₁) (e₂ : A₂ ⟶ B₂) (he₁ : IsIso e₁) (he₂ : IsIso e₂)
    (h₁ : f ≫ e₂ = e₁ ≫ f') (h₂ : g = e₂ ≫ g') (hex : (ShortComplex.mk f' g' w').Exact) :
    (ShortComplex.mk f g w).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk f g w) (S₂ := ShortComplex.mk f' g' w')
    { τ₁ := e₁, τ₂ := e₂, τ₃ := 𝟙 A₃, comm₁₂ := h₁.symm,
      comm₂₃ := h₂.symm.trans (Category.comp_id _).symm }).2 hex

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Space

section Generic

-- As in `ConormalModuleComposition.lean`: unfolding the inverse image to its construction does
-- not terminate, and is not needed to compare the two spellings of its objects.
attribute [local irreducible] modulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS} (g : X ⟶ X') (g' : X' ⟶ X'')
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1)
    (Z'' : ClosedSubspaces B S hS X''.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (f' : (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z''.1.toFunctor, Z''.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hsq' : subspaceInclusion B S hS X' Z' ≫ g' = f' ≫ subspaceInclusion B S hS X'' Z'')

/-- **The left-hand square comparing two stacked conormal maps with the map of ideal sheaves.**
For two vertically stacked commutative squares of closed subspaces, the inverse image along `f`
of the conormal map of the lower square, followed by the comparison `f^*ι_{Z'}^* ≅ ι_Z^*g^*` of
the upper square, is the comparison of the two left-hand terms followed by the inverse image of
the map `g'^*𝓘_{Z''} ⟶ 𝓘_{Z'}` of ideal sheaves: naturality of the comparison. -/
theorem conormalMap_comp_conormalPullbackComparison :
    (modulePullback B S hS f).map (conormalMap B S hS Z' Z'' g' f' hsq') ≫
        conormalPullbackComparison B S hS Z Z' g f hsq =
      ((modulePullback B S hS f).map (conormalPullbackComparison B S hS Z' Z'' g' f' hsq') ≫
          (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules)) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq')) := by
  have hnat : (modulePullback B S hS f).map
          ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).map
            (idealSheafMap B S hS Z' Z'' g' f' hsq')) ≫
        (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
          (definingIdealSheaf B S hS X' Z').toSheafOfModules =
      (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.app
            ((modulePullback B S hS g').obj
              (definingIdealSheaf B S hS X'' Z'').toSheafOfModules) ≫
        (modulePullback B S hS (subspaceInclusion B S hS X Z)).map
          ((modulePullback B S hS g).map (idealSheafMap B S hS Z' Z'' g' f' hsq')) :=
    (conormalPullbackCompIso B S hS Z Z' g f hsq).hom.naturality
      (idealSheafMap B S hS Z' Z'' g' f' hsq')
  refine Eq.trans (eq_whisker ((modulePullback B S hS f).map_comp
    (conormalPullbackComparison B S hS Z' Z'' g' f' hsq')
    ((modulePullback B S hS (subspaceInclusion B S hS X' Z')).map
      (idealSheafMap B S hS Z' Z'' g' f' hsq')))
    (conormalPullbackComparison B S hS Z Z' g f hsq)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact whisker_eq _ hnat

end Generic

section IdealLevel

/-- The abelian structure of the category of `𝒪_X`-modules on the small étale site, with its
universes written out.  Instance search in this file's import closure otherwise tries Mathlib's
`SheafOfModules` instance at an unsolved module universe and stops on the universe constraint
`u + 1 =?= max (u + 1) ?v`; this local instance is that same instance at the universe `u`. -/
private noncomputable local instance (priority := high) modulesAbelian (B : BigFppfSite.{u})
    (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS F hF)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS F hF)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M N : AlgebraicSpaces B S hS} (h : M ⟶ N) (Y : ClosedSubspaces B S hS N.1)
    (Z : ClosedSubspaces B S hS M.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS M Z ≫ h = f ≫ subspaceInclusion B S hS N Y)

include hsq in
/-- A closed subspace `Z ⊆ M` whose inclusion followed by `h` factors through `Y` lies in the
inverse image `h⁻¹(Y)`. -/
theorem le_preimageSubspace_of_square : Z.1 ≤ (preimageSubspace B S hS h Y).1 := by
  intro U x hx
  have e := congrArg (fun t => t.hom.app U ⟨x, hx⟩) hsq
  change h.hom.app U x = Y.1.ι.app U (f.hom.app U ⟨x, hx⟩) at e
  change h.hom.app U x ∈ Y.1.obj U
  rw [e]
  exact (f.hom.app U ⟨x, hx⟩).2

/-- The inverse image `h⁻¹(Y)` of the square, as an algebraic space. -/
noncomputable abbrev squareFibre : AlgebraicSpaces B S hS :=
  ⟨(preimageSubspace B S hS h Y).1.toFunctor, (preimageSubspace B S hS h Y).2.1⟩

/-- The inclusion `j : h⁻¹(Y) ⟶ M`. -/
noncomputable abbrev squareFibreInclusion : squareFibre B S hS h Y ⟶ M :=
  subspaceInclusion B S hS M (preimageSubspace B S hS h Y)

/-- The copy `W = j⁻¹(Z)` of `Z` inside `h⁻¹(Y)`. -/
noncomputable abbrev squareSub : ClosedSubspaces B S hS (squareFibre B S hS h Y).1 :=
  preimageSubspace B S hS (squareFibreInclusion B S hS h Y) Z

include hsq in
/-- When `Z ⊆ h⁻¹(Y)`, the inclusion of `Z` lifts through `W = j⁻¹(Z) ⟶ h⁻¹(Y) ⟶ M`. -/
noncomputable def squareSubSection :
    (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(squareSub B S hS h Y Z).1.toFunctor, (squareSub B S hS h Y Z).2.1⟩ :
        AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk
    { app U := ↾fun z => ⟨⟨z.1, le_preimageSubspace_of_square B S hS h Y Z f hsq U z.2⟩, z.2⟩
      naturality _ _ _ := rfl }

/-- The lift of `Z` through `W ⟶ h⁻¹(Y) ⟶ M` is a lift. -/
theorem squareSubSection_comp :
    squareSubSection B S hS h Y Z f hsq ≫
        subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) ≫
          squareFibreInclusion B S hS h Y =
      𝟙 _ ≫ subspaceInclusion B S hS M Z :=
  rfl

include hsq in
/-- **The kernel of the structure map of `W ⟶ h⁻¹(Y) ⟶ M` is the defining ideal of `Z`.** -/
theorem kernelIdealSheaf_squareSub_comp :
    kernelIdealSheaf B S hS
        (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) ≫
          squareFibreInclusion B S hS h Y) =
      definingIdealSheaf B S hS M Z := by
  refine le_antisymm ?_ ?_
  · have := kernelIdealSheaf_le_comp B S hS (𝟙 _) _ (squareSubSection B S hS h Y Z f hsq)
      (subspaceInclusion B S hS M Z) (squareSubSection_comp B S hS h Y Z f hsq).symm
    rwa [Category.id_comp] at this
  · exact kernelIdealSheaf_le_comp B S hS _ (subspaceInclusion B S hS M Z) _
      (squareFibreInclusion B S hS h Y)
      (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z)

/-- The composite `𝒪_M ⟶ j_*𝒪_{h⁻¹(Y)} ⟶ j_*ι_*𝒪_W` of the two canonical projections. -/
noncomputable abbrev squareStructureComp :
    SheafOfModules.unit (structureRingSheaf B S hS M) ⟶
      (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).obj
        (structureSheafPushforward B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))) :=
  pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y) ≫
    (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
      (pushforwardStructureProjection B S hS
        (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)))

/-- On sections, the composite of the two canonical projections is the structure map of the
composite `W ⟶ h⁻¹(Y) ⟶ M` read through the composition comparison of direct images: this is
`AlgebraicGeometry.Space.structureSharpSet_comp`. -/
theorem structureSharp_squareSub_comp_app (U : (SmallEtale B S hS M.1)ᵒᵖ)
    (t : (structureSetSheaf B S hS M).obj.obj U) :
    (structureSharpSet B S hS
        (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) ≫
          squareFibreInclusion B S hS h Y)).hom.app U t =
      ((smallToposMorphismTypeU_comp B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))
          (squareFibreInclusion B S hS h Y)).hom.app
        (structureSetSheaf B S hS _)).hom.app U
        ((squareStructureComp B S hS h Y Z).val.app U t) :=
  (Sheaf.hom_congr_app_apply (structureSharpSet_comp B S hS
    (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))
    (squareFibreInclusion B S hS h Y)) U t).symm

include hsq in
/-- **A function killed by the composite projection lies in the defining ideal of `Z`.** -/
theorem mem_definingIdealSheaf_of_squareStructureComp (U : (SmallEtale B S hS M.1)ᵒᵖ)
    (s : (SheafOfModules.unit (structureRingSheaf B S hS M)).val.obj U)
    (hs : (squareStructureComp B S hS h Y Z).val.app U s = 0) :
    s ∈ (definingIdealSheaf B S hS M Z).obj U := by
  rw [← kernelIdealSheaf_squareSub_comp B S hS h Y Z f hsq]
  change ((structureSharp B S hS
    (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) ≫
      squareFibreInclusion B S hS h Y)).hom.app U).hom s = 0
  let z : (SheafOfModules.unit (structureRingSheaf B S hS M)).val.obj U := 0
  have h0 : (squareStructureComp B S hS h Y Z).val.app U s =
      (squareStructureComp B S hS h Y Z).val.app U z := hs.trans (map_zero _).symm
  refine (structureSharp_squareSub_comp_app B S hS h Y Z U s).trans ?_
  rw [h0, ← structureSharp_squareSub_comp_app B S hS h Y Z U z]
  exact map_zero (((structureSharp B S hS
    (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) ≫
      squareFibreInclusion B S hS h Y)).hom.app U).hom)

/-- The defining ideal sheaf of a closed subspace, as an object of the category of
`𝒪_X`-modules.  Writing the objects of a short complex at this spelling is what lets instance
search find the zero morphisms of the category of modules. -/
noncomputable abbrev idealModule (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1) :
    Modules.{u, u} B S hS X.1 X.2 :=
  (definingIdealSheaf B S hS X Z).toSheafOfModules

/-- The map `idealSheafMap` of the square of `W ⊆ h⁻¹(Y)` over `Z ⊆ M`, transposed along
`j^* ⊣ j_*`: a morphism `𝓘_Z ⟶ j_*𝓘_W` of `𝒪_M`-modules. -/
noncomputable abbrev squareIdealTranspose :
    idealModule B S hS M Z ⟶
      (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).obj
        (idealModule B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)) :=
  (modulePullbackAdjunction B S hS (squareFibreInclusion B S hS h Y)).homEquiv _ _
    (idealSheafMap B S hS (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
      (preimageProjection B S hS (squareFibreInclusion B S hS h Y) Z)
      (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z))

/-- **The transposed map of ideal sheaves is the restriction of the projection.**  Followed by
the direct image of the inclusion `𝓘_W ⊆ 𝒪_{h⁻¹(Y)}`, the map `𝓘_Z ⟶ j_*𝓘_W` is the inclusion
`𝓘_Z ⊆ 𝒪_M` followed by the projection `𝒪_M ⟶ j_*𝒪_{h⁻¹(Y)}`: both are pullback of regular
functions on chart diagrams. -/
theorem squareIdealTranspose_comp_ι :
    squareIdealTranspose B S hS h Y Z ≫
        (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
          (definingIdealSheaf B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)).ι =
      (definingIdealSheaf B S hS M Z).ι ≫
        pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y) := by
  apply (modulePushforwardHomEquiv B S hS (squareFibreInclusion B S hS h Y) _ _).injective
  refine ModuleFMap.ext B S hS (funext fun d => funext fun s => ?_)
  refine (modulePushforwardHomEquiv_app_comp_right B S hS (squareFibreInclusion B S hS h Y)
    (squareIdealTranspose B S hS h Y Z)
    (definingIdealSheaf B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)).ι d s).trans ?_
  refine Eq.trans (congrArg (fun t => (definingIdealSheaf B S hS (squareFibre B S hS h Y)
      (squareSub B S hS h Y Z)).ι.val.app (op d.U) t)
    (congrFun (congrFun (congrArg ModuleFMap.app (idealSheafMap_transpose B S hS
      (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
      (preimageProjection B S hS (squareFibreInclusion B S hS h Y) Z)
      (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z))) d) s)) ?_
  refine Eq.trans ?_ (modulePushforwardHomEquiv_app_comp_left B S hS
    (squareFibreInclusion B S hS h Y) (definingIdealSheaf B S hS M Z).ι
    (pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y)) d s).symm
  exact ((moduleChartProjection_app_structureSharp B S hS (squareFibreInclusion B S hS h Y)
    d.V _ s.1).trans (chartPullback_indexOfChartDiagram B S hS
      (squareFibreInclusion B S hS h Y) d s.1)).symm

include hsq in
/-- The defining ideal of `h⁻¹(Y)` is contained in that of `Z`. -/
theorem definingIdealSheaf_preimageSubspace_le :
    definingIdealSheaf B S hS M (preimageSubspace B S hS h Y) ≤ definingIdealSheaf B S hS M Z :=
  definingIdealSheaf_antitone B S hS M Z (preimageSubspace B S hS h Y)
    (le_preimageSubspace_of_square B S hS h Y Z f hsq)

/-- The inclusion `𝓘_{h⁻¹(Y)} ⟶ 𝓘_Z` of defining ideal sheaves. -/
noncomputable def squareIdealInclusion :
    idealModule B S hS M (preimageSubspace B S hS h Y) ⟶ idealModule B S hS M Z :=
  (definingIdealSheaf B S hS M Z).factorThru
    (definingIdealSheaf B S hS M (preimageSubspace B S hS h Y)).ι
    fun U x => definingIdealSheaf_preimageSubspace_le B S hS h Y Z f hsq U x.2

/-- The inclusion `𝓘_{h⁻¹(Y)} ⟶ 𝓘_Z` followed by `𝓘_Z ⊆ 𝒪_M` is the inclusion of `𝓘_{h⁻¹(Y)}`. -/
theorem squareIdealInclusion_ι :
    squareIdealInclusion B S hS h Y Z f hsq ≫ (definingIdealSheaf B S hS M Z).ι =
      (definingIdealSheaf B S hS M (preimageSubspace B S hS h Y)).ι :=
  SheafOfModules.Submodule.factorThru_ι _ _ _

/-- The inclusion of a defining ideal sheaf is a monomorphism in `AlgebraicGeometry.Space.Modules`,
the category of `𝒪_X`-modules this file works in. -/
theorem mono_definingIdealSheaf_ι_modules (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    Mono (C := Modules.{u, u} B S hS X.1 X.2) (definingIdealSheaf B S hS X Z).ι :=
  (SheafOfModules.forget _).mono_of_mono_map
    (inferInstanceAs (Mono (definingIdealSheaf B S hS X Z).toSubmodule.ι))

/-- The inclusion `𝓘_{h⁻¹(Y)} ⟶ 𝓘_Z` is a monomorphism. -/
theorem mono_squareIdealInclusion :
    Mono (C := Modules.{u, u} B S hS M.1 M.2) (squareIdealInclusion B S hS h Y Z f hsq) := by
  have := mono_definingIdealSheaf_ι_modules B S hS M (preimageSubspace B S hS h Y)
  exact mono_of_mono_fac (squareIdealInclusion_ι B S hS h Y Z f hsq)

/-- The direct image along `j` of the inclusion `𝓘_W ⊆ 𝒪_{h⁻¹(Y)}` is a monomorphism. -/
theorem mono_modulePushforward_map_squareSub_ι :
    Mono (C := Modules.{u, u} B S hS M.1 M.2)
      ((modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
        (definingIdealSheaf B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)).ι) := by
  have := mono_definingIdealSheaf_ι_modules B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)
  have := (modulePullbackAdjunction B S hS
    (squareFibreInclusion B S hS h Y)).rightAdjoint_preservesLimits.{0, 0}
  exact Functor.map_mono _ _

/-- The direct image along `j` of `𝓘_W ⟶ 𝒪_{h⁻¹(Y)} ⟶ ι_*𝒪_W` is zero. -/
theorem modulePushforward_map_squareSub_ι_comp :
    (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
        (definingIdealSheaf B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)).ι ≫
      (modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
        (pushforwardStructureProjection B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))) = 0 := by
  have := modulePushforward_additive B S hS (squareFibreInclusion B S hS h Y)
  refine (Functor.map_comp _ _ _).symm.trans ?_
  refine ((modulePushforward B S hS (squareFibreInclusion B S hS h Y)).congr_map
    (SheafOfModules.Submodule.ker_ι_comp (pushforwardStructureProjection B S hS
      (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))))).trans ?_
  exact Functor.map_zero _ _ _

/-- The ideal-level sequence is a complex. -/
theorem squareIdealInclusion_comp_squareIdealTranspose :
    squareIdealInclusion B S hS h Y Z f hsq ≫ squareIdealTranspose B S hS h Y Z = 0 := by
  have := mono_modulePushforward_map_squareSub_ι B S hS h Y Z
  refine (cancel_mono ((modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
    (definingIdealSheaf B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)).ι)).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => squareIdealInclusion B S hS h Y Z f hsq ≫ t)
    (squareIdealTranspose_comp_ι B S hS h Y Z)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ pushforwardStructureProjection B S hS
    (squareFibreInclusion B S hS h Y)) (squareIdealInclusion_ι B S hS h Y Z f hsq)).trans ?_
  exact (SheafOfModules.Submodule.ker_ι_comp
    (pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y))).trans
    zero_comp.symm

/-- **The ideal-level sequence `𝓘_{h⁻¹(Y)} ⟶ 𝓘_Z ⟶ j_*𝓘_W ⟶ 0` on `M` is exact**, and its
right-hand map is an epimorphism. -/
theorem exact_and_epi_squareIdealTranspose :
    (ShortComplex.mk (C := Modules.{u, u} B S hS M.1 M.2) _ _
        (squareIdealInclusion_comp_squareIdealTranspose B S hS h Y Z f hsq)).Exact ∧
      Epi (C := Modules.{u, u} B S hS M.1 M.2) (squareIdealTranspose B S hS h Y Z) := by
  have : Epi (C := Modules.{u, u} B S hS M.1 M.2)
      (pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y)) :=
    epi_pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y)
      (preimageSubspace B S hS h Y).2.2
  have := mono_definingIdealSheaf_ι_modules B S hS M Z
  have := mono_squareIdealInclusion B S hS h Y Z f hsq
  refine @Abelian.exact_and_epi_of_kernel_comp (Modules.{u, u} B S hS M.1 M.2) _
    (modulesAbelian B S hS M.1 M.2) _ _ _ _ _ _
    (pushforwardStructureProjection B S hS (squareFibreInclusion B S hS h Y)) _
    ((modulePushforward B S hS (squareFibreInclusion B S hS h Y)).map
      (pushforwardStructureProjection B S hS
        (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))))
    (definingIdealSheaf B S hS M Z).ι _ (fun {T} x hx => ?_) _
    (mono_modulePushforward_map_squareSub_ι B S hS h Y Z)
    (modulePushforward_map_squareSub_ι_comp B S hS h Y Z)
    (definingIdealSheaf B S hS M (preimageSubspace B S hS h Y)).ι (fun {T} x hx => ?_)
    (squareIdealInclusion B S hS h Y Z f hsq) _ (squareIdealInclusion_ι B S hS h Y Z f hsq)
    (squareIdealTranspose B S hS h Y Z) (squareIdealTranspose_comp_ι B S hS h Y Z) _
  · refine ⟨(definingIdealSheaf B S hS M Z).factorThru x fun U t =>
      mem_definingIdealSheaf_of_squareStructureComp B S hS h Y Z f hsq U _
        ((congrArg (fun m => m.val.app U t) hx).trans rfl), ?_⟩
    exact SheafOfModules.Submodule.factorThru_ι _ _ _
  · refine ⟨(definingIdealSheaf B S hS M (preimageSubspace B S hS h Y)).factorThru x
      fun U t => by
        change ((structureSharp B S hS (squareFibreInclusion B S hS h Y)).hom.app U).hom
          (x.val.app U t) = 0
        exact (congrArg (fun m => m.val.app U t) hx).trans rfl, ?_⟩
    exact SheafOfModules.Submodule.factorThru_ι _ _ _

/-- **The map of ideal sheaves of the square factors through the ideal of `h⁻¹(Y)`.**  The map
`h^*𝓘_Y ⟶ 𝓘_Z` of Stacks 04CP is the map `h^*𝓘_Y ⟶ 𝓘_{h⁻¹(Y)}` of the fibre product square
followed by the inclusion `𝓘_{h⁻¹(Y)} ⊆ 𝓘_Z`: both read inside `𝒪_M` as the inverse image of the
inclusion `𝓘_Y ⊆ 𝒪_N`, by `AlgebraicGeometry.Space.idealSheafMap_comp_definingIdealSheaf_ι`. -/
theorem idealSheafMap_eq_comp_squareIdealInclusion :
    idealSheafMap B S hS Z Y h f hsq =
      idealSheafMap B S hS (preimageSubspace B S hS h Y) Y h (preimageProjection B S hS h Y)
          (conormalEtaleRestrictionSquare B S hS h Y) ≫
        squareIdealInclusion B S hS h Y Z f hsq := by
  have := mono_definingIdealSheaf_ι_modules B S hS M Z
  refine (cancel_mono (C := Modules.{u, u} B S hS M.1 M.2)
    (definingIdealSheaf B S hS M Z).ι).1 ?_
  refine (idealSheafMap_comp_definingIdealSheaf_ι B S hS Z Y h f hsq).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun t => idealSheafMap B S hS (preimageSubspace B S hS h Y) Y h
    (preimageProjection B S hS h Y) (conormalEtaleRestrictionSquare B S hS h Y) ≫ t)
    (squareIdealInclusion_ι B S hS h Y Z f hsq)).symm
  exact (idealSheafMap_comp_definingIdealSheaf_ι B S hS (preimageSubspace B S hS h Y) Y h
    (preimageProjection B S hS h Y) (conormalEtaleRestrictionSquare B S hS h Y)).symm

/-- The ideal-level sequence `h^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_W` is a complex. -/
theorem idealSheafMap_comp_squareIdealTranspose :
    idealSheafMap B S hS Z Y h f hsq ≫ squareIdealTranspose B S hS h Y Z = 0 := by
  refine (congrArg (fun t => t ≫ squareIdealTranspose B S hS h Y Z)
    (idealSheafMap_eq_comp_squareIdealInclusion B S hS h Y Z f hsq)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => idealSheafMap B S hS (preimageSubspace B S hS h Y) Y h
    (preimageProjection B S hS h Y) (conormalEtaleRestrictionSquare B S hS h Y) ≫ t)
    (squareIdealInclusion_comp_squareIdealTranspose B S hS h Y Z f hsq)).trans ?_
  exact comp_zero

/-- **The ideal-level conormal sequence of a square, `h^*𝓘_Y ⟶ 𝓘_Z ⟶ j_*𝓘_W ⟶ 0`, is exact.** -/
theorem exact_idealSheafMap_squareIdealTranspose :
    (ShortComplex.mk (C := Modules.{u, u} B S hS M.1 M.2) _ _
        (idealSheafMap_comp_squareIdealTranspose B S hS h Y Z f hsq)).Exact := by
  let φ : ShortComplex.mk (C := Modules.{u, u} B S hS M.1 M.2) _ _
        (idealSheafMap_comp_squareIdealTranspose B S hS h Y Z f hsq) ⟶
      ShortComplex.mk (C := Modules.{u, u} B S hS M.1 M.2) _ _
        (squareIdealInclusion_comp_squareIdealTranspose B S hS h Y Z f hsq) :=
    { τ₁ := idealSheafMap B S hS (preimageSubspace B S hS h Y) Y h
        (preimageProjection B S hS h Y) (conormalEtaleRestrictionSquare B S hS h Y)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (idealSheafMap_eq_comp_squareIdealInclusion B S hS h Y Z f hsq).symm.trans
        (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := epi_idealSheafMap B S hS h Y
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2
    (exact_and_epi_squareIdealTranspose B S hS h Y Z f hsq).1

/-- The inverse image of a vanishing composite of modules is a vanishing composite. -/
private theorem modulePullback_map_comp_eq_zero {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    {A₁ A₂ A₃ : Modules.{u, u} B S hS X'.1 X'.2} (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (w : a ≫ b = 0) :
    (modulePullback B S hS g).map a ≫ (modulePullback B S hS g).map b = 0 := by
  have := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  rw [← Functor.map_comp, w, Functor.map_zero]

/-- The inverse image preserves exactness of a complex of modules with epimorphic right map. -/
private theorem exact_map_modulePullback_of_epi {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    {T : ShortComplex (Modules.{u, u} B S hS X'.1 X'.2)} (hex : T.Exact) (hepi : Epi T.g) :
    (T.map (modulePullback B S hS g)).Exact := by
  have := (modulePullbackAdjunction B S hS g).isLeftAdjoint
  have := (modulePullbackAdjunction B S hS g).leftAdjoint_preservesColimits.{0, 0}
  exact hex.map_of_epi_of_preservesCokernel _ hepi inferInstance

/-- The map `idealSheafMap` of the square of `W ⊆ h⁻¹(Y)` over `Z ⊆ M`, the right-hand map of
the ideal-level sequence on `h⁻¹(Y)`. -/
noncomputable abbrev squareIdealMap :
    (modulePullback B S hS (squareFibreInclusion B S hS h Y)).obj (idealModule B S hS M Z) ⟶
      idealModule B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z) :=
  idealSheafMap B S hS (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
    (preimageProjection B S hS (squareFibreInclusion B S hS h Y) Z)
    (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z)

/-- The inverse image along `j` of the transposed map, followed by the counit, is the map of
ideal sheaves itself. -/
theorem modulePullback_map_squareIdealTranspose_comp_counit :
    (modulePullback B S hS (squareFibreInclusion B S hS h Y)).map
        (squareIdealTranspose B S hS h Y Z) ≫
      (modulePullbackAdjunction B S hS (squareFibreInclusion B S hS h Y)).counit.app
        (idealModule B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z)) =
      squareIdealMap B S hS h Y Z :=
  ((modulePullbackAdjunction B S hS (squareFibreInclusion B S hS h Y)).homEquiv_counit
    _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

/-- The ideal-level sequence on `h⁻¹(Y)` is a complex. -/
theorem modulePullback_map_idealSheafMap_comp_squareIdealMap :
    (modulePullback B S hS (squareFibreInclusion B S hS h Y)).map
        (idealSheafMap B S hS Z Y h f hsq) ≫ squareIdealMap B S hS h Y Z = 0 := by
  refine (congrArg (fun t => (modulePullback B S hS (squareFibreInclusion B S hS h Y)).map
    (idealSheafMap B S hS Z Y h f hsq) ≫ t)
    (modulePullback_map_squareIdealTranspose_comp_counit B S hS h Y Z)).symm.trans ?_
  rw [← Category.assoc, modulePullback_map_comp_eq_zero B S hS _ _ _
    (idealSheafMap_comp_squareIdealTranspose B S hS h Y Z f hsq), zero_comp]

/-- **The ideal-level conormal sequence on `h⁻¹(Y)`, `j^*h^*𝓘_Y ⟶ j^*𝓘_Z ⟶ 𝓘_W ⟶ 0`, is
exact.**  It is the inverse image along `j` of the sequence on `M`, the inverse image being right
exact, read through the counit at `𝓘_W`, which is an isomorphism because `j` is a closed
immersion (Stacks 04CJ, part (2)). -/
theorem exact_modulePullback_map_idealSheafMap_squareIdealMap :
    (ShortComplex.mk (C := Modules.{u, u} B S hS (squareFibre B S hS h Y).1
        (squareFibre B S hS h Y).2) _ _
        (modulePullback_map_idealSheafMap_comp_squareIdealMap B S hS h Y Z f hsq)).Exact := by
  have := (modulePullbackAdjunction B S hS (squareFibreInclusion B S hS h Y)).isLeftAdjoint
  have hex := exact_map_modulePullback_of_epi B S hS (squareFibreInclusion B S hS h Y)
    (exact_idealSheafMap_squareIdealTranspose B S hS h Y Z f hsq)
    (exact_and_epi_squareIdealTranspose B S hS h Y Z f hsq).2
  have hiso := isIso_modulePullbackAdjunction_counit B S hS (squareFibreInclusion B S hS h Y)
    (preimageSubspace B S hS h Y).2.2
    (idealModule B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))
  let φ : (ShortComplex.mk (C := Modules.{u, u} B S hS M.1 M.2) _ _
        (idealSheafMap_comp_squareIdealTranspose B S hS h Y Z f hsq)).map
        (modulePullback B S hS (squareFibreInclusion B S hS h Y)) ⟶
      ShortComplex.mk (C := Modules.{u, u} B S hS (squareFibre B S hS h Y).1
        (squareFibre B S hS h Y).2) _ _
        (modulePullback_map_idealSheafMap_comp_squareIdealMap B S hS h Y Z f hsq) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (modulePullbackAdjunction B S hS (squareFibreInclusion B S hS h Y)).counit.app
        (idealModule B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))
      comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := (Category.id_comp _).trans
        (modulePullback_map_squareIdealTranspose_comp_counit B S hS h Y Z).symm }
  have : Mono φ.τ₃ := @IsIso.mono_of_iso _ _ _ _ _ hiso
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex

/-- The projection `π : W ⟶ Z` of `W = j⁻¹(Z)`. -/
noncomputable abbrev squareSubProjection :
    (⟨(squareSub B S hS h Y Z).1.toFunctor, (squareSub B S hS h Y Z).2.1⟩ :
      AlgebraicSpaces B S hS) ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  preimageProjection B S hS (squareFibreInclusion B S hS h Y) Z

/-- The ideal-level sequence on `W`: the inverse image along `ι_W` of the one on `h⁻¹(Y)`. -/
theorem modulePullback_map_squareIdeal_comp_eq_zero :
    (modulePullback B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))).map
        ((modulePullback B S hS (squareFibreInclusion B S hS h Y)).map
          (idealSheafMap B S hS Z Y h f hsq)) ≫
      (modulePullback B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))).map
        (squareIdealMap B S hS h Y Z) = 0 :=
  modulePullback_map_comp_eq_zero B S hS _ _ _
    (modulePullback_map_idealSheafMap_comp_squareIdealMap B S hS h Y Z f hsq)

/-- **The ideal-level conormal sequence on `W`, `ι_W^*j^*h^*𝓘_Y ⟶ ι_W^*j^*𝓘_Z ⟶ ι_W^*𝓘_W ⟶ 0`,
is exact**: the inverse image along `ι_W` of the sequence on `h⁻¹(Y)`, the inverse image being
right exact. -/
theorem exact_modulePullback_map_squareIdeal :
    (ShortComplex.mk (C := Modules.{u, u} B S hS (squareSub B S hS h Y Z).1.toFunctor
        (squareSub B S hS h Y Z).2.1) _ _
        (modulePullback_map_squareIdeal_comp_eq_zero B S hS h Y Z f hsq)).Exact := by
  have hepi : Epi (C := Modules.{u, u} B S hS (squareFibre B S hS h Y).1
      (squareFibre B S hS h Y).2) (squareIdealMap B S hS h Y Z) :=
    epi_idealSheafMap B S hS (squareFibreInclusion B S hS h Y) Z
  have hex := exact_map_modulePullback_of_epi B S hS
    (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))
    (exact_modulePullback_map_idealSheafMap_squareIdealMap B S hS h Y Z f hsq) hepi
  exact hex

end IdealLevel

/-- Exactness of a short complex does not depend on the instance of zero morphisms it is formed
with, there being only one. -/
theorem _root_.CategoryTheory.ShortComplex.exact_mk_congr_hasZeroMorphisms {C : Type*}
    [Category C] (I₁ I₂ : HasZeroMorphisms C) {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (w₁ : f ≫ g = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (@HasZeroMorphisms.zero C _ I₁ _ _)))
    (w₂ : f ≫ g = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (@HasZeroMorphisms.zero C _ I₂ _ _)))
    (h : @ShortComplex.Exact C _ I₁ (@ShortComplex.mk C _ I₁ _ _ _ f g w₁)) :
    @ShortComplex.Exact C _ I₂ (@ShortComplex.mk C _ I₂ _ _ _ f g w₂) := by
  obtain rfl := Subsingleton.elim I₁ I₂
  exact h

/-- The vanishing of a composite does not depend on the instance of zero morphisms. -/
theorem _root_.CategoryTheory.Limits.comp_eq_zero_congr_hasZeroMorphisms {C : Type*}
    [Category C] (I₁ I₂ : HasZeroMorphisms C) {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (w₂ : f ≫ g = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (@HasZeroMorphisms.zero C _ I₂ _ _))) :
    f ≫ g = @OfNat.ofNat _ 0 (@Zero.toOfNat0 _ (@HasZeroMorphisms.zero C _ I₁ _ _)) := by
  obtain rfl := Subsingleton.elim I₁ I₂
  exact w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {M N : AlgebraicSpaces B S hS} (h : M ⟶ N) (Y : ClosedSubspaces B S hS N.1)
    (Z : ClosedSubspaces B S hS M.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS M Z ≫ h = f ≫ subspaceInclusion B S hS N Y)

section Comparison

attribute [local irreducible] modulePullback

/-- `AlgebraicGeometry.Space.modulePullback_map_squareIdeal_comp_eq_zero` at the zero morphisms
found outside the ideal-level section. -/
alias modulePullback_map_squareIdeal_comp_eq_zero' := modulePullback_map_squareIdeal_comp_eq_zero

/-- The left-hand square of the comparison. -/
theorem conormalMap_square_left_comm :
    (modulePullback B S hS (squareSubProjection B S hS h Y Z)).map
        (conormalMap B S hS Z Y h f hsq) ≫
      conormalPullbackComparison B S hS (squareSub B S hS h Y Z) Z
        (squareFibreInclusion B S hS h Y) (squareSubProjection B S hS h Y Z)
        (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z) =
      ((modulePullback B S hS (squareSubProjection B S hS h Y Z)).map
          (conormalPullbackComparison B S hS Z Y h f hsq) ≫
        (conormalPullbackCompIso B S hS (squareSub B S hS h Y Z) Z
          (squareFibreInclusion B S hS h Y) (squareSubProjection B S hS h Y Z)
          (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z)).hom.app
            ((modulePullback B S hS h).obj (definingIdealSheaf B S hS N Y).toSheafOfModules)) ≫
        (modulePullback B S hS
          (subspaceInclusion B S hS (squareFibre B S hS h Y) (squareSub B S hS h Y Z))).map
          ((modulePullback B S hS (squareFibreInclusion B S hS h Y)).map
            (idealSheafMap B S hS Z Y h f hsq)) :=
  conormalMap_comp_conormalPullbackComparison B S hS
    (squareFibreInclusion B S hS h Y) h (squareSub B S hS h Y Z) Z Y
    (squareSubProjection B S hS h Y Z) f
    (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z) hsq

/-- Exactness of the conormal sequence of a square, with the vanishing of the composite as a
hypothesis.  The sequence is compared with the inverse image along `ι_W` of the ideal-level
sequence on `h⁻¹(Y)`, by the comparison isomorphisms of
`AlgebraicGeometry.Space.conormalPullbackCompIso`. -/
theorem exact_conormalMap_square_of_comp_eq_zero
    (w : (modulePullback B S hS (squareSubProjection B S hS h Y Z)).map
        (conormalMap B S hS Z Y h f hsq) ≫
      conormalMap B S hS (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
        (squareSubProjection B S hS h Y Z)
        (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z) = 0) :
    (ShortComplex.mk _ _ w).Exact := by
  have hiso₁ : IsIso ((modulePullback B S hS (squareSubProjection B S hS h Y Z)).map
          (conormalPullbackComparison B S hS Z Y h f hsq) ≫
        (conormalPullbackCompIso B S hS (squareSub B S hS h Y Z) Z
          (squareFibreInclusion B S hS h Y) (squareSubProjection B S hS h Y Z)
          (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z)).hom.app
            ((modulePullback B S hS h).obj (definingIdealSheaf B S hS N Y).toSheafOfModules)) := by
    have := isIso_conormalPullbackComparison B S hS Z Y h f hsq
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) (Iso.isIso_hom (((conormalPullbackCompIso
      B S hS (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
      (squareSubProjection B S hS h Y Z)
      (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z))).app _))
  have hiso₂ := isIso_conormalPullbackComparison B S hS (squareSub B S hS h Y Z) Z
    (squareFibreInclusion B S hS h Y) (squareSubProjection B S hS h Y Z)
    (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z)
  exact ShortComplex.exact_of_isIso_comm _ _ w _ _
    (modulePullback_map_squareIdeal_comp_eq_zero' B S hS h Y Z f hsq) _ _ hiso₁ hiso₂
    (conormalMap_square_left_comm B S hS h Y Z f hsq)
    (conormalMap_eq B S hS (squareSub B S hS h Y Z) Z
      (squareFibreInclusion B S hS h Y) (squareSubProjection B S hS h Y Z)
      (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z))
    (ShortComplex.exact_mk_congr_hasZeroMorphisms _ _ _ _ _ _
      (exact_modulePullback_map_squareIdeal B S hS h Y Z f hsq))

end Comparison

/-- **The conormal sequence of a square is a complex.**  The composite of
`π^*f^*𝒞_{Y/N} ⟶ π^*𝒞_{Z/M}` and `π^*𝒞_{Z/M} ⟶ 𝒞_{W/h⁻¹(Y)}` is zero: the ambient morphism
`h⁻¹(Y) ⟶ M ⟶ N` of the outer rectangle factors through `Y`. -/
theorem conormalMap_square_comp_eq_zero :
    (modulePullback B S hS (squareSubProjection B S hS h Y Z)).map
        (conormalMap B S hS Z Y h f hsq) ≫
      conormalMap B S hS (squareSub B S hS h Y Z) Z (squareFibreInclusion B S hS h Y)
        (squareSubProjection B S hS h Y Z)
        (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z) = 0 :=
  comp_conormalMap_eq_zero_of_factors B S hS (squareFibreInclusion B S hS h Y) h
    (squareSub B S hS h Y Z) Z Y (squareSubProjection B S hS h Y Z) f
    (conormalEtaleRestrictionSquare B S hS (squareFibreInclusion B S hS h Y) Z) hsq
    (preimageProjection B S hS h Y) (conormalEtaleRestrictionSquare B S hS h Y)

/-- **Exactness in the middle of the conormal sequence of a square.**  Let `h : M ⟶ N` be a
morphism of algebraic spaces, `Y ⊆ N` and `Z ⊆ M` closed subspaces and `f : Z ⟶ Y` a morphism
with `Z ⟶ M ⟶ N` equal to `Z ⟶ Y ⟶ N`.  Let `W = j⁻¹(Z)` be the copy of `Z` inside the fibre
product `h⁻¹(Y) = Y ×_N M`, with projection `π : W ⟶ Z`.  Then the sequence

`π^*f^*𝒞_{Y/N} ⟶ π^*𝒞_{Z/M} ⟶ 𝒞_{W/h⁻¹(Y)} ⟶ 0`

of maps of Stacks 04CP is exact. -/
theorem exact_conormalMap_square :
    (ShortComplex.mk _ _ (conormalMap_square_comp_eq_zero B S hS h Y Z f hsq)).Exact :=
  ShortComplex.exact_mk_congr_hasZeroMorphisms _ _ _ _ _ _
    (exact_conormalMap_square_of_comp_eq_zero B S hS h Y Z f hsq
      (comp_eq_zero_congr_hasZeroMorphisms _ _ _ _
        (conormalMap_square_comp_eq_zero B S hS h Y Z f hsq)))

end AlgebraicGeometry.Space

end
