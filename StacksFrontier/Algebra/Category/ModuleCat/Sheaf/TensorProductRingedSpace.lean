module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct
public import Mathlib.Geometry.RingedSpace.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The tensor product of `𝒪_X`-modules on a ringed space

Let `(X, 𝒪_X)` be a ringed space and `ℱ`, `𝒢` sheaves of `𝒪_X`-modules. Stacks 01CA defines
the tensor product presheaf `ℱ ⊗_{p, 𝒪_X} 𝒢 : U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)` and the tensor product
sheaf `ℱ ⊗_{𝒪_X} 𝒢 = (ℱ ⊗_{p, 𝒪_X} 𝒢)^#`, characterises it by
`Hom_{𝒪_X}(ℱ ⊗_{𝒪_X} 𝒢, ℋ) = Bilin_{𝒪_X}(ℱ × 𝒢, ℋ)`, and records the canonical symmetry and
associativity isomorphisms, functorial in all arguments.

The tensor product sheaf is `Stacks.SheafOfModules.Tensor.sheafTensor`, constructed over an
arbitrary site; this file states each assertion of the section at the opens of a ringed space,
where the standing hypotheses of the site-level constructions (existence of sheafification of
abelian presheaves, sheaf conditions for the forgetful functors) are discharged by instances.

## Main definitions

* `Stacks.SheafOfModules.bilinFunctor`: the functor `ℋ ↦ Bilin_𝒪(ℱ × 𝒢, ℋ)` of bilinear maps
  of sheaves of modules, on any site.
* `Stacks.SheafOfModules.TensorRingedSpace.tensorCorepresentableBy`: `ℱ ⊗_{𝒪_X} 𝒢`
  corepresents `ℋ ↦ Bilin_{𝒪_X}(ℱ × 𝒢, ℋ)`.
* `Stacks.SheafOfModules.TensorRingedSpace.tensorSymmetry`: the symmetry
  `ℱ ⊗_{𝒪_X} 𝒢 ≅ 𝒢 ⊗_{𝒪_X} ℱ` as an isomorphism of bifunctors.
* `Stacks.SheafOfModules.TensorRingedSpace.tensorAssociativity`: the associativity
  `(ℱ ⊗ 𝒢) ⊗ ℋ ≅ ℱ ⊗ (𝒢 ⊗ ℋ)` as an isomorphism of trifunctors.

## Main results

* `Stacks.SheafOfModules.TensorRingedSpace.tensorPresheaf_sections` and
  `Stacks.SheafOfModules.TensorRingedSpace.tensorPresheaf_restrict_tmul`: the tensor product
  presheaf has sections `ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)` and the induced restriction maps.
* `Stacks.SheafOfModules.TensorRingedSpace.tensorSheaf_eq_sheafification`: the tensor product
  sheaf is the sheafification of the tensor product presheaf.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0GIG](https://stacks.math.columbia.edu/tag/0GIG)
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.Sheaf TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

universe w v u

namespace Stacks.SheafOfModules

section BilinFunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- The functor `ℋ ↦ Bilin_𝒪(A × B, ℋ)` of bilinear maps of sheaves of modules: a morphism
`ℋ ⟶ ℋ'` acts by post-composition. -/
noncomputable def bilinFunctor (A B : SheafOfModules.{w} R) :
    SheafOfModules.{w} R ⥤ Type (max u w) where
  obj N := { q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N // IsBilinearPairing R q }
  map {N N'} k := TypeCat.ofHom fun
    (q : { q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N // IsBilinearPairing R q }) ↦
      (⟨q.1 ≫ (moduleSheafFunctor R).map k, q.2.comp k⟩ :
        { q : moduleSheaf R A ⨯ moduleSheaf R B ⟶ moduleSheaf R N' // IsBilinearPairing R q })
  map_id N := by
    apply ConcreteCategory.hom_ext
    intro q
    exact Subtype.ext ((congrArg (q.1 ≫ ·) ((moduleSheafFunctor R).map_id N)).trans
      (Category.comp_id _))
  map_comp k k' := by
    apply ConcreteCategory.hom_ext
    intro q
    exact Subtype.ext ((congrArg (q.1 ≫ ·) ((moduleSheafFunctor R).map_comp k k')).trans
      (Category.assoc _ _ _).symm)

variable (A B : SheafOfModules.{w} R)

@[simp]
lemma bilinFunctor_map_coe {N N' : SheafOfModules.{w} R} (k : N ⟶ N')
    (q : (bilinFunctor R A B).obj N) :
    ((bilinFunctor R A B).map k q).1 = q.1 ≫ (moduleSheafFunctor R).map k :=
  rfl

end BilinFunctor

namespace TensorRingedSpace

variable (X : RingedSpace.{u, u})

/-- The sheaf of rings of a ringed space, as a sheaf of commutative rings on the site of opens
of `X`. -/
abbrev structureSheaf : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} :=
  ⟨X.presheaf, X.IsSheaf⟩

variable {X}
variable (F G : SheafOfModules.{u} (Tensor.ringSheaf (structureSheaf X)))

/-- **The tensor product presheaf** `ℱ ⊗_{p, 𝒪_X} 𝒢` assigns to an open `U ⊂ X` the
`𝒪_X(U)`-module `ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`. -/
@[stacks 01CA "the section's tensor product presheaf `F ⊗_{p, O_X} G`, the rule which assigns
to `U ⊂ X` open the `O_X(U)`-module `F(U) ⊗_{O_X(U)} G(U)`: its sections"]
theorem tensorPresheaf_sections (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    ((PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val).obj U : Type u) =
      (F.val.obj U ⊗[(Tensor.ringSheaf (structureSheaf X)).obj.obj U] G.val.obj U) :=
  rfl

/-- The restriction maps of the tensor product presheaf are the tensor products of the
restriction maps of `ℱ` and `𝒢`. -/
@[stacks 01CA "the section's tensor product presheaf `F ⊗_{p, O_X} G`: its restriction maps,
`x ⊗ y ↦ x|_V ⊗ y|_V`"]
theorem tensorPresheaf_restrict_tmul {U V : (TopologicalSpace.Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (x : F.val.obj U) (y : G.val.obj U) :
    (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val).restrictₛₗ f
        (x ⊗ₜ[(Tensor.ringSheaf (structureSheaf X)).obj.obj U] y) =
      F.val.restrictₛₗ f x ⊗ₜ[(Tensor.ringSheaf (structureSheaf X)).obj.obj V]
        G.val.restrictₛₗ f y :=
  PresheafOfModules.tensorObj_restrictₛₗ_tmul f x y

/-- **The tensor product sheaf** `ℱ ⊗_{𝒪_X} 𝒢` is the sheafification
`(ℱ ⊗_{p, 𝒪_X} 𝒢)^#` of the tensor product presheaf. -/
@[stacks 01CA "the section's definition of the tensor product sheaf as the sheafification
`F ⊗_{O_X} G = (F ⊗_{p, O_X} G)^#` of the tensor product presheaf"]
theorem tensorSheaf_eq_sheafification :
    ((Tensor.sheafTensor (structureSheaf X)).obj F).obj G =
      (PresheafOfModules.sheafification (R := Tensor.ringSheaf (structureSheaf X))
        (𝟙 (Tensor.ringSheaf (structureSheaf X)).obj)).obj
        (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) :=
  rfl

/-- **The tensor product sheaf represents bilinear maps.** For every sheaf of `𝒪_X`-modules
`ℋ`, morphisms `ℱ ⊗_{𝒪_X} 𝒢 ⟶ ℋ` are in natural bijection with bilinear maps
`ℱ × 𝒢 → ℋ` of sheaves of `𝒪_X`-modules: `ℱ ⊗_{𝒪_X} 𝒢` corepresents the functor
`ℋ ↦ Bilin_{𝒪_X}(ℱ × 𝒢, ℋ)`, which characterises it up to unique isomorphism. -/
@[stacks 01CA "the characterisation of `F ⊗_{O_X} G` as the sheaf of `O_X`-modules with
`Hom_{O_X}(F ⊗_{O_X} G, H) = Bilin_{O_X}(F × G, H)` for every `O_X`-module `H`, naturally in
`H`: the tensor product sheaf corepresents `H ↦ Bilin_{O_X}(F × G, H)`"]
noncomputable def tensorCorepresentableBy :
    (bilinFunctor (Tensor.ringSheaf (structureSheaf X)) F G).CorepresentableBy
      (((Tensor.sheafTensor (structureSheaf X)).obj F).obj G) where
  homEquiv {N} := (bilinearEquivTensorHom (A := F) (B := G) (N := N)).symm
  homEquiv_comp {N N'} k φ := by
    refine (Equiv.symm_apply_eq _).mpr ?_
    exact ((bilinearEquivTensorHom_naturality
      ((bilinearEquivTensorHom (A := F) (B := G) (N := N)).symm φ) k).trans
      (congrArg (· ≫ k) (Equiv.apply_symm_apply _ _))).symm

/-- **The symmetry of the tensor product sheaf**: the canonical isomorphism
`ℱ ⊗_{𝒪_X} 𝒢 ≅ 𝒢 ⊗_{𝒪_X} ℱ`, functorial in `ℱ` and `𝒢`, i.e. an isomorphism between the
tensor bifunctor and its flip. It is the sheafification of the sectionwise symmetry
`M ⊗_R N ≅ N ⊗_R M` of the tensor product of modules. -/
@[stacks 01CA "the symmetry `F ⊗_{O_X} G = G ⊗_{O_X} F`, functorial in `F` and `G`: an
isomorphism of the tensor bifunctor with its flip, induced by the symmetry of tensor products of
modules"]
noncomputable def tensorSymmetry :
    Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X) ≅
      (Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X)).flip :=
  Tensor.sheafTensorBraiding (structureSheaf X)

/-- **The associativity of the tensor product sheaf**: the canonical isomorphism
`(ℱ ⊗_{𝒪_X} 𝒢) ⊗_{𝒪_X} ℋ ≅ ℱ ⊗_{𝒪_X} (𝒢 ⊗_{𝒪_X} ℋ)`, functorial in `ℱ`, `𝒢` and `ℋ`, i.e.
an isomorphism of trifunctors. It is induced through sheafification by the associativity of
tensor products of modules. -/
@[stacks 01CA "the associativity `(F ⊗_{O_X} G) ⊗_{O_X} H = F ⊗_{O_X} (G ⊗_{O_X} H)`,
functorial in `F`, `G` and `H`: an isomorphism of trifunctors, induced by the associativity of
tensor products of modules"]
noncomputable def tensorAssociativity :
    bifunctorComp₁₂ (Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X))
        (Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X)) ≅
      bifunctorComp₂₃ (Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X))
        (Tensor.sheafTensor.{u, u, u, u, u} (structureSheaf X)) :=
  sheafTensorAssociator (structureSheaf X)

end TensorRingedSpace

end Stacks.SheafOfModules
