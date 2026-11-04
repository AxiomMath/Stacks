module

public import StacksFrontier.AlgebraicGeometry.BaseChange.Hypercovering
public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.FiniteProducts
public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.Affine
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechComparison

/-!
# The complex of sections of a hypercovering under base change by a module

Consider a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine, `F` a quasi-coherent `𝒪_X`-module and `G` a quasi-coherent
`𝒪_{S'}`-module which is flat over `S`. Let `K` be a simplicial semi-representable object over
`⊤ ⊆ X` which is finite in every degree and all of whose members are affine opens, and let
`K' = K ⋙ baseChangeFormalCoproduct g' ⊤` be its base change. This file identifies the complex of
sections of `K'` with coefficients in `F' = (f')^* G ⊗ (g')^* F` with the base change of the
complex of sections of `K` with coefficients in `F`:

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} s(F(K))  ≅  s(F'(K'))`

as complexes of `Γ(S', ⊤)`-modules.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.baseChangeOver`: the base change functor on the
  opens over `⊤`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonDeg`: the degreewise comparison.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonPresheaf`: the degreewise comparisons
  assembled into a morphism of presheaves of `Γ(S', ⊤)`-modules on the opens over `⊤ ⊆ X`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.sectionsComplexBaseChangeIso`: **the isomorphism of
  complexes.**

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonDeg_apply`: the degreewise comparison on a
  pure tensor is the product of the two pullbacks.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_comparisonPresheaf_app` and
  `Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_cochainComplexFunctor_map_comparisonPresheaf`:
  the comparison is an isomorphism at an open with affine source, hence induces an isomorphism of
  the complexes of sections of a semi-representable object with affine members.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.cochainComplexFunctor_baseChange`: the complex of
  sections of the base change of `K` with coefficients in a presheaf is the complex of sections
  of `K` with coefficients in the pulled-back presheaf, as an equality.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.FormalCoproduct
open ComplexShape MonoidalCategory Opposite Simplicial TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.CategoryTheory.Hypercovering
open scoped TensorProduct

attribute [local instance] ModuleCat.hasLimitsOfSize
attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### The base change of the opens over the whole space -/

/-- **The base change functor on the opens over an open `V` of `X`**: an open `Z ⊆ V` is sent to
its preimage `(g')⁻¹Z ⊆ (g')⁻¹V`. -/
abbrev baseChangeOver (g' : X' ⟶ X) (V : X.Opens) : Over V ⥤ Over (g' ⁻¹ᵁ V) :=
  Over.post (Opens.map g'.base)

/-- **The complex of sections of a base-changed simplicial semi-representable object** is the
complex of sections of the original one with coefficients in the pulled-back presheaf (an
equality of complexes). -/
theorem cochainComplexFunctor_baseChange {C D : Type u} [Category.{u} C] [Category.{u} D]
    {A : Type u} [Category.{u} A] [Preadditive A] [HasProducts.{u} A] (u : D ⥤ C)
    (K : SimplicialObject (FormalCoproduct.{u} D)) (P : Cᵒᵖ ⥤ A) :
    (cochainComplexFunctor.{u} (K ⋙ mapFormalCoproduct.{u} u)).obj P =
      (cochainComplexFunctor.{u} K).obj (u.op ⋙ P) :=
  rfl

/-! ### The degreewise comparison in the shape of the complex -/

variable {g : S' ⟶ S} {f : X ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}

/-- **The degreewise comparison**, from the base change of the sections of `F` over `Z` to the
sections of `(f')^* G ⊗ (g')^* F` over the preimage of `Z`. -/
def comparisonDeg (H : IsPullback g' f' f g) (F : X.Modules) (G : S'.Modules)
    (Z : Over (⊤ : X.Opens)) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    (baseRestrictScalars f ⋙
          Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).obj
        (((SectionsOver.sectionsModulePresheafFunctor X.ringCatSheaf ⊤).obj F).obj (op Z)) ⟶
      (baseRestrictScalars f').obj
        (((SectionsOver.sectionsModulePresheafFunctor X'.ringCatSheaf ⊤).obj
          (tensorPullback g' f' F G)).obj (op ((baseChangeOver g' ⊤).obj Z))) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  letI := baseModule f F Z.left
  letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ Z.left)
  (Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).map (rescaleSource f F Z).hom ≫
    ModuleCat.ofHom (comparisonMap g' f' F G H Z.left) ≫
      (rescaleTarget f' (tensorPullback g' f' F G) ((baseChangeOver g' ⊤).obj Z)).hom

/-- **The degreewise comparison on a pure tensor** is `comparisonSection`. -/
theorem comparisonDeg_apply (H : IsPullback g' f' f g) (F : X.Modules) (G : S'.Modules)
    (Z : Over (⊤ : X.Opens)) (n : Γ(G, ⊤)) (a : Γ(F, Z.left)) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    (comparisonDeg H F G Z).hom (n ⊗ₜ[Γ(S, ⊤)] a) =
      comparisonSection g' f' F G Z.left n a :=
  rfl

/-- **The degreewise comparisons form a morphism of presheaves of `Γ(S', ⊤)`-modules** on the
opens over `⊤ ⊆ X`: they commute with restriction. -/
def comparisonPresheaf (H : IsPullback g' f' f g) (F : X.Modules) (G : S'.Modules) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    (SectionsOver.sectionsModulePresheafFunctor X.ringCatSheaf ⊤).obj F ⋙
        (baseRestrictScalars f ⋙
          Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)) ⟶
      (baseChangeOver g' ⊤).op ⋙
        ((SectionsOver.sectionsModulePresheafFunctor X'.ringCatSheaf ⊤).obj
            (tensorPullback g' f' F G) ⋙
          baseRestrictScalars f') :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  { app Z := comparisonDeg H F G Z.unop
    naturality := by
      intro Z₁ Z₂ φ
      refine Stacks.TensorBimodule.hom_ext Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤) (fun n a => ?_)
      exact (comparisonSection_res g' f' F G (leOfHom φ.unop.left) n a).symm }

/-- **The comparison is an isomorphism at an open with affine source.** -/
theorem isIso_comparisonPresheaf_app [IsAffine S] [IsAffine S'] (H : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (Z : (Over (⊤ : X.Opens))ᵒᵖ) (hZ : IsAffineOpen Z.unop.left) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    IsIso ((comparisonPresheaf H F G).app Z) := by
  let := baseAlgebra g
  let := baseModule g G ⊤
  let := coeffTower g G
  let := baseModule f F Z.unop.left
  let := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ Z.unop.left)
  have hbij := bijective_comparisonMap_of_isAffineOpen H F G hZ
  have h : (comparisonPresheaf H F G).app Z =
      ((Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).mapIso
            (rescaleSource f F Z.unop) ≪≫
          (LinearEquiv.ofBijective (comparisonMap g' f' F G H Z.unop.left) hbij).toModuleIso ≪≫
          rescaleTarget f' (tensorPullback g' f' F G)
            ((baseChangeOver g' ⊤).obj Z.unop)).hom := rfl
  rw [h]
  exact Iso.isIso_hom _

/-! ### The isomorphism of complexes -/

/-- **The comparison induces an isomorphism of the complexes of sections** of a simplicial
semi-representable object all of whose members are affine opens. -/
theorem isIso_cochainComplexFunctor_map_comparisonPresheaf [IsAffine S] [IsAffine S']
    (H : IsPullback g' f' f g) (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules)
    [G.IsQuasicoherent] (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))
    (haff : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    IsIso ((cochainComplexFunctor.{u} K).map (comparisonPresheaf H F G)) :=
  let := baseAlgebra g
  let := baseModule g G ⊤
  let := coeffTower g G
  Stacks.CechPushforward.isIso_cochainComplexFunctor_map.{u} K (comparisonPresheaf H F G)
    (fun n i ↦ isIso_comparisonPresheaf_app H F G (op ((K.obj (op ⦋n⦌)).obj i)) (haff n i))

/-- **The complex of sections of a hypercovering under base change by a module.**  Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `S` and `S'` affine, let `F` be a quasi-coherent
`𝒪_X`-module and `G` a quasi-coherent `𝒪_{S'}`-module whose global sections are flat over
`Γ(S, ⊤)`, and let `K` be a simplicial semi-representable object over `⊤ ⊆ X` which is finite in
every degree and all of whose members are affine opens.  Then

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} s(F(K)) ≅ s(((f')^* G ⊗ (g')^* F)(K'))`

as complexes of `Γ(S', ⊤)`-modules, where `K'` is the base change of `K`. -/
def sectionsComplexBaseChangeIso [IsAffine S] [IsAffine S'] (H : IsPullback g' f' f g)
    (F : X.Modules) [F.IsQuasicoherent] (G : S'.Modules) [G.IsQuasicoherent]
    (hflat : letI := baseModule g G ⊤; Module.Flat Γ(S, ⊤) Γ(G, ⊤))
    (K : SimplicialObject (FormalCoproduct.{u} (Over (⊤ : X.Opens))))
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I)
    (haff : ∀ (n : ℕ) (i : (K.obj (op ⦋n⦌)).I), IsAffineOpen ((K.obj (op ⦋n⦌)).obj i).left) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    letI := coeffTower g G
    (((baseRestrictScalars f ⋙
            Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)).mapHomologicalComplex
          (up ℕ)).obj (SectionsOver.sectionsModuleComplex.{u} X.ringCatSheaf ⊤ K F)) ≅
      ((baseRestrictScalars f').mapHomologicalComplex (up ℕ)).obj
        (SectionsOver.sectionsModuleComplex.{u} X'.ringCatSheaf ⊤
          (K ⋙ baseChangeFormalCoproduct.{u} g' ⊤) (tensorPullback g' f' F G)) :=
  letI := baseAlgebra g
  letI := baseModule g G ⊤
  letI := coeffTower g G
  letI := hflat
  haveI : PreservesFiniteLimits (Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)) :=
    Stacks.TensorBimodule.preservesFiniteLimits_of_flat Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)
  haveI := isIso_cochainComplexFunctor_map_comparisonPresheaf H F G K haff
  (Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite.{u}
        (baseRestrictScalars f ⋙ Stacks.TensorBimodule.functor Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤)) K hfin
        (fun J _ ↦ Stacks.CechPushforward.preservesLimitsOfShape_discrete_of_preservesFiniteLimits
          _ J)).app
      ((SectionsOver.sectionsModulePresheafFunctor X.ringCatSheaf ⊤).obj F) ≪≫
    asIso ((cochainComplexFunctor.{u} K).map (comparisonPresheaf H F G)) ≪≫
    ((Stacks.CechPushforward.cochainComplexFunctorCompMapHomologicalComplexIsoOfFinite.{u}
          (baseRestrictScalars f') (K ⋙ baseChangeFormalCoproduct.{u} g' ⊤) hfin
          (fun J _ ↦
            Stacks.CechPushforward.preservesLimitsOfShape_discrete_of_preservesFiniteLimits
              _ J)).app
        ((SectionsOver.sectionsModulePresheafFunctor X'.ringCatSheaf ⊤).obj
          (tensorPullback g' f' F G))).symm

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
